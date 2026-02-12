#include "Constraint_database.inlines.hpp"
#include "Linear_solver.inlines.hpp"
#include "../dpllx/SATSolver.h"
#include "../arithmeticSolver.defs.hpp"

using namespace FF;


bool Linear_solver::ok() {

  // Dimensions of basis / tableau / related objects match.
  if (int(row2cnt.size())    != initial->row_dimension())  return false;
  if (basis->row_dimension() != tableau->row_dimension())  return false;
  if (basis->row_dimension() != initial->row_dimension())  return false;
  if (basis->row_dimension() != int(pos2lin.size()) + 1)   return false;
  if (basis->col_dimension() != tableau->col_dimension())  return false;
  if (basis->col_dimension() != initial->col_dimension())  return false;
  if (basis->col_dimension() != number_variables() + 1)    return false;

  // Dimensions of abstraction related objects match.
  if (idx2mon.size() != idx2cnt.size()) return false;
  if (idx2mon.size() != idx2rnk.size()) return false;
  if (pos2lin.size() != pos2rnk.size()) return false;

  // idx2mon and mon2idx are inverses one another.
  if (idx2mon.size() != mon2idx.size()) return false;
  for (const auto& [mon, idx] : mon2idx) {
    if (idx < 0 or idx >= int(idx2mon.size())) return false;
    if (mon != idx2mon[idx]) return false;
  }

  // pos2lin and lin2pos are inverses one another.
  if (pos2lin.size() != lin2pos.size()) return false;
  for (const auto& [lin, pos] : lin2pos) {
    if (pos < 0 or pos >= int(pos2lin.size())) return false;
    if (lin != pos2lin[pos]) return false;
  }

  // idx2rnk, pos2rnk, rnk2idx_pos satisfy the expected relation.
  if (rnk2idx_pos.size() != idx2rnk.size() + pos2rnk.size()) return false;
  for (int rnk = 0; rnk < int(rnk2idx_pos.size()); ++rnk)
    if (rnk2idx_pos[rnk].second) { // Monomial
      int idx = rnk2idx_pos[rnk].first;
      if (idx < 0 or idx >= int(idx2rnk.size())) return false;
      if (idx2rnk[idx] != rnk) return false;
    }
    else {
      int pos = rnk2idx_pos[rnk].first;
      if (pos < 0 or pos >= int(pos2rnk.size())) return false;
      if (pos2rnk[pos] != rnk) return false;
    }

  // pvar2cns, pvar2var satisfy the expected relation.
  if (pvar2cns.size() != pvar2var.size()) return false;

  for (const auto& [pvar, cns] : pvar2cns) {
    auto it = pvar2var.find(pvar);
    if (it == pvar2var.end()) return false;
    int var = it->second;
    Polynomial<Zp> q;
    if (cns != 0) q = q + Polynomial((-1) * cns, Monomial());
    if (is_linear_expression_variable(var)) {
      const Linear_expression& lin = linear_expression(var);
      for (const auto& [v, c] : lin) {
        if      (is_monomial_variable(v)) q = q + Polynomial(c, monomial(v));
        else if (is_original_variable(v)) q = q + Polynomial(c, Monomial(v));
        else return false;
      }
    }
    else if (is_monomial_variable(var)) q = q + Polynomial(Zp(1), monomial(var));
    else if (is_original_variable(var)) q = q + Polynomial(Zp(1), Monomial(var));
    else return false;

    q.normalize();
    if (q != s.cons_db.polynomial(pvar)) return false;
  }

  // var2pvars, pvar2var satisfy the expected relation.
  if (int(var2pvars.size()) != number_variables()) return false;
  int sum = 0;
  for (int v = 0; v < number_variables(); ++v) {
    const vector<int>& pvars = var2pvars[v];
    for (int p : pvars) if (pvar2var[p] != v) return false;
    sum += pvars.size();
  }

  if (sum != s.cons_db.size()) return false;

  // trail, equals_to, diff_from satisfy the expected relation.
  for (int i = 0; i < int(trail.size()); ++i) {
    const Domain_constraint& dc = trail[i];
    if (not dc.valid()) continue;
    int x = dc.variable;
    if (dc.equal) {
      const auto& eqs = equals_to[x];
      auto it = find(eqs.begin(), eqs.end(), i);
      if (it == eqs.end()) return false;
    }
    else {
      const auto& dis = diff_from[x];
      auto it = find(dis.begin(), dis.end(), i);
      if (it == dis.end()) return false;
    }
  }

  for (int x = 0; x < int(equals_to.size()); ++x) {
    const auto& eqs = equals_to[x];
    for (int i : eqs) {
      if (i < 0 or i > int(trail.size())) return false;
      const Domain_constraint& dc = trail[i];
      if (x != dc.variable or not dc.equal) return false;
    }
    auto checked = [&](int i) { return i < next_chck; };
    if (count_if(eqs.begin(), eqs.end(), checked) > 1) return false;
  }

  for (int x = 0; x < int(diff_from.size()); ++x) {
    const auto& dis = diff_from[x];
    for (int i : dis) {
      if (i < 0 or i > int(trail.size())) return false;
      const Domain_constraint& dc = trail[i];
      if (x != dc.variable or dc.equal) return false;
    }
  }

  // next_chck can be at most the size of the trail.
  if (next_chck > int(trail.size())) return false;

  // next_prop can be at most next_chck.
  if (next_prop > next_chck)         return false;

  // Solution satisfies the equalities and the domain constraints of non-basic variables.
  if (not solution_satisfies_equalities())                                return false;

  if (not solution_satisfies_domain_constraints_of_non_basic_variables()) return false;

  // For each row of the initial tableau, row2cnt gives the number of non-fixed variables in that row
  // considering *propagated* literals.

  // For each monomial, idx2cnt gives the number of non-fixed variables in that monomial
  // considering *propagated* literals.

  vector<int> tmp_row2cnt( initial->row_dimension() );
  for (int r = 1; r < initial->row_dimension(); ++r) {
    tmp_row2cnt[r] = initial->row_size(r);
  }

  vector<int> tmp_idx2cnt( idx2cnt.size() );
  for (int i = 0; i < int(idx2cnt.size()); ++i) {
    tmp_idx2cnt[i] = idx2mon[i].size();
  }

  for (int i = 0; i < next_prop; ++i) {
    const Domain_constraint& dc = trail[i];
    if (not dc.valid()) continue;
    if (not dc.equal)   continue;
    int         x = dc.variable;

    int c = x + 1;  // + 1 for the offset of columns in the tableau.
    for (auto i = initial->col_beg(c), ie = initial->col_end(c); i != ie; i.next(*initial)) {
      int r = initial->index(i);
      --tmp_row2cnt[r];
    }
    if (is_original_variable(x))
      for (int i : var2indices[x])
	--tmp_idx2cnt[i];
  }

  for (int r = 1; r < initial->row_dimension(); ++r) {
    if (tmp_row2cnt[r] != row2cnt[r]) {

      cerr << "Row " << r << ":";
      for (auto j = initial->row_beg(r), e = initial->row_end(r); j != e; j.next(*initial)) {
	int c = initial->index(j);
	int x = c - 1;
	cerr << "+ (" << initial->value(j) << ") * [" << to_string(x) << "]";
      }
      cerr << " == 0" << endl;

      for (auto j = initial->row_beg(r), e = initial->row_end(r); j != e; j.next(*initial)) {
	int c = initial->index(j);
	int x = c - 1;
        const auto& eqs = equals_to[x];
        auto propagated = [&](int i) { return i < next_prop; };
        auto it = find_if(eqs.begin(), eqs.end(), propagated);
        if (it != eqs.end()) {
          cerr << "Variable " << to_string(x) << " fixed" << endl;
        }
      }

      cerr << "Error: row #" << r << " has " << tmp_row2cnt[r]
	   << " non-fixed variables instead of " << row2cnt[r] << endl;
      return false;
    }
  }

  for (int i = 0; i < int(idx2cnt.size()); ++i) {
    if (tmp_idx2cnt[i] != idx2cnt[i]) {
      cerr << "Error: monomial " << idx2mon[i] << " has " << tmp_idx2cnt[i]
	   << " non-fixed variables instead of " << idx2cnt[i] << endl;
      return false;
    }
  }

  // var2indices[x] is the list of indices of monomials m s.t. original variable x occurs in m.
  map<int, set<int> > var2indexes;
  for (int idx = 0; idx < int(idx2mon.size()); ++idx) {
    const Monomial& mon = idx2mon[idx];
    for (const auto& [u, e] : mon) {
      if (e <= 0) return false;
      var2indexes[u].insert(idx);
    }
  }

  for (int u = 0; u < int(var2indices.size()); ++u) {
    const auto& indices = var2indices[u];
    if (var2indexes[u] != set<int>(indices.begin(), indices.end())) return false;
  }

  for (const auto& [lit, exp] : s.plit2exp) {
    if (lit != Lit(1, true) and exp.empty()) {
      cerr << "Error: " << s.to_string(lit) << " has an empty explanation" << endl;
      return false;
    }
  }

  return true;
}


Linear_solver::~Linear_solver() {

  if (tableau) delete tableau;
  if (initial) delete initial;
  if (basis)   delete basis;
}


int Linear_solver::variable(const Monomial& mon) {

  int num_vars = s.get_num_vars();
  FF_ASSERT(LINEAR, not is_one(mon));
  if (is_nonlinear(mon)) {
    int sz = idx2mon.size();
    auto [it, added] = mon2idx.insert({mon, sz});
    if (added) {
      FF_ASSERT(LINEAR, idx2mon.size() == idx2rnk.size());
      idx2mon.push_back(mon);
      idx2rnk.push_back(rnk2idx_pos.size());

      idx2cnt.push_back(0);
      for (const auto& [u, _] : mon) {
        const auto& eqs = equals_to[u];
        auto jt = find_equality(eqs);
        if (jt == eqs.end()) ++idx2cnt.back();
      }

      for (const auto& [u, _] : mon)
	var2indices[u].push_back(sz);

      rnk2idx_pos.push_back({sz, true});
      var2pvars.push_back({});
    }
    return num_vars + idx2rnk[it->second];
  }
  else { // Don't introduce auxiliary variable if monomial is already linear (i.e. a variable).
    FF_ASSERT(LINEAR, mon.begin() != mon.end());
    const auto& [u, e] = *mon.begin();
    FF_ASSERT(LINEAR, e == 1);
    return u;
  }
}


int Linear_solver::variable(const Linear_expression& lin) {

  int num_vars = s.get_num_vars();
  FF_ASSERT(LINEAR, not lin.empty());
  if (lin.size() != 1) {
    int sz = pos2lin.size();
    auto [it, added] = lin2pos.insert({lin, sz});
    if (added) {
      FF_ASSERT(LINEAR, pos2lin.size() == pos2rnk.size());
      pos2lin.push_back(lin);
      pos2rnk.push_back(rnk2idx_pos.size());
      rnk2idx_pos.push_back({sz, false});
      var2pvars.push_back({});
    }
    return num_vars + pos2rnk[it->second];
  }
  else { // Don't introduce auxiliary variable if linear expression is already linear (i.e. a variable).
    FF_ASSERT(LINEAR, lin.begin() != lin.end());
    const auto& [u, c] = *lin.begin();
    FF_ASSERT(LINEAR, is_one(c));
    return u;
  }
}


void Linear_solver::defineNewEquality(int pvar, const Polynomial<Zp>& poly) {

  FF_ASSERT(LINEAR, poly.is_normalized());

  int old_vars = number_variables();

  var2indices.resize( s.get_num_vars() ); // Only original variables.

  Linear_expression lin;
  Zp cnt(0);
  for (const auto& [mon, coe] : poly)
    if (is_one(mon)) cnt = -coe;              // Move the constant term to the other side of equality.
    else lin.push_back({variable(mon), coe}); // Abstract nonlinear monomials if present.

  int var = variable(lin); // Propositional variable pvar is equivalent to equality var == cnt.
  pvar2var[pvar] = var;
  pvar2cns[pvar] = cnt;

  var2pvars[var].push_back(pvar);

  int new_vars = number_variables(); // May have added e.g. new monomial / linear expression variables.

  sol      .resize(new_vars);
  equals_to.resize(new_vars);
  diff_from.resize(new_vars);

  for (int v = old_vars; v < new_vars; ++v) { // For each of the new variables...

    tableau->insert_new_col();
    initial->insert_new_col();
    basis  ->insert_new_col();

    if (is_linear_expression_variable(v)) {

      const auto& e = linear_expression(v);

      tableau->insert_new_row(); // Add equality e == v to tableau, etc.
      initial->insert_new_row();
      row2cnt.push_back(0);

      // Move the auxiliary variable v to the other side of the equality.
      tableau->insert_to_last_row(Zp(-1), v + 1); // +1 for the offset of columns in the tableau.
      initial->insert_to_last_row(Zp(-1), v + 1);

      const auto& eqs = equals_to[v];
      auto it = find_equality(eqs);
      if (it == eqs.end()) ++row2cnt.back();

      Zp eval = 0;
      for (const auto& [w, c] : e) {
	tableau->insert_to_last_row(c, w + 1);  // +1 for the offset of columns in the tableau.
	initial->insert_to_last_row(c, w + 1);

        const auto& eqs = equals_to[w];
        auto it = find_equality(eqs);
        if (it == eqs.end()) ++row2cnt.back();

	eval += sol[w] * c;
      }
      sol[v] = eval;

      // v is chosen as basic variable of the new row.
      int r = tableau->row_dimension() - 1;
      vector<int> cols; // To eliminate all other basic variables in the new row.
      for (auto j = tableau->row_beg(r), ej = tableau->row_end(r); j != ej; j.next(*tableau)) {
	int cj = tableau->index(j);
	int xj = cj - 1;
	if (xj != v) {
	  int rj = basis->row(cj);
	  if (rj != WRONG_INDEX)
	    cols.push_back(cj);
	}
      }
      for (int cj : cols) {
	int rj = basis->row(cj);
	FF_ASSERT(LINEAR, rj != WRONG_INDEX);
	tableau->add_mul(tableau->value(rj, cj), r, - tableau->value(r, cj), rj);
      }
      basis->insert_new_row(v + 1); // +1 for the offset.
    }
    else FF_ASSERT(LINEAR, is_monomial_variable(v)); // v cannot be an original variable.
  }
}


void Linear_solver::initializeAfterParsing() {

  int n_vars = s.get_num_vars();  // Original variables.

  sol      .resize(n_vars);
  equals_to.resize(n_vars);
  diff_from.resize(n_vars);
  var2pvars.resize(n_vars);

  // Due to the implementation of matrices, column 0 and row 0 cannot be used.
  // So we must apply an offset of +1 / -1 when moving from variables to columns and vice versa.
  // tableau = new F_matrix(n_vars + 1, 1); // +1, 1 for the offset of rows in the tableau.
  tableau = new C_matrix(n_vars + 1); // +1, 1 for the offset of rows in the tableau.

  initial = new C_matrix(n_vars + 1);
  basis   = new Basis   (n_vars + 1);    // +1 for the offset of columns in the tableau.
  basis->insert_new_row(0);              // Setting dummy variable as basic variable of dummy row.

  for (const auto& [pvar, poly] : s.cons_db) {
    FF_ASSERT(LINEAR, poly.is_normalized());
    defineNewEquality(pvar, poly);
  }

#if FF_PRINT
  cout << endl;
  for (int v = 0; v < number_variables(); ++v) {
    const vector<int>& pvars = var2pvars[v];
    if (pvars.empty()) continue;
    cout << "[" << to_string(v) << "]" << endl << " appears in propositional variable(s):";
    for (int p : pvars) cout << " " << p;
    cout << endl;
  }
#endif

  FF_ASSERT(LINEAR, ok());
}


int Linear_solver::checkConsistency(int level) {

  constexpr int      SAT = 0;
  constexpr int  UNKNOWN = 1;
  
#if FF_PRINT
  string tab(3, ' ');
  FF_OUT(LINEAR, tab << "BEGIN trail " << endl);
  for (int idx = 0; idx < int(trail.size()); ++idx) {
    const Domain_constraint& dc = trail[idx];
    FF_OUT(LINEAR, tab << idx << tab);
    if (dc.valid())  {FF_OUT(LINEAR, to_string(dc) << endl);}
    else             {FF_OUT(LINEAR,    "----"     << endl);}
  }
  FF_OUT(LINEAR, tab << "END trail" << endl);
#endif

  FF_ASSERT(LINEAR, ok());

  while (next_chck < int(trail.size())) {
    int idx = next_chck;
    const Domain_constraint& dc = trail[idx];
    if (dc.valid()) {
      int res = check_domain_constraint(idx);
      if (res < 0) return res;
    }
    ++next_chck;
  }
  FF_ASSERT(LINEAR, ok());

  int res = check_consistency_heavy(); // Make a heavy-weight consistency check.

  if (level == 0 and res == SAT) { // At a leaf, ensure that the solution satisfies nonlinear semantics.

    FF_ASSERT(LINEAR, ok());
    FF_ASSERT(LINEAR, solution_satisfies_domain_constraints_of_basic_variables());

    if (solution_compatible_with_nonlinear_monomials()) {

      print_solution();

      // Copy to the solver the projection of the solution on original variables.
      s.solution.clear();
      for (int v = 0; v < s.get_num_vars(); ++v) {
	ostringstream out;
	out << Context::Variable(v);
	s.solution[out.str()] = sol[v];
      }
    }
    else res = UNKNOWN; // Spurious model.
  }
  return res;
}


int Linear_solver::check_consistency_heavy() {

  FF_OUT(LINEAR, "In check_consistency_heavy..." << endl);

  constexpr int      SAT = 0;
  constexpr int  UNKNOWN = 1;
  
  const int threshold = 500;

  int res = UNKNOWN;

  // While unknown, i.e., not conflicting and not satisfied, do ...
  for (int ites = 0; res == UNKNOWN and ites < threshold; ++ites) {

    FF_ASSERT(LINEAR, ok());

    bool found = false; // Found a basic variable whose assigned value violates domain constraints?
    for (auto i = basis->beg(), ei = basis->end(); res == UNKNOWN and not found and i != ei; i.next(*basis)) {
      int cx = basis->col(i);
      if (cx == 0) continue; // Ignore the dummy column 0 (which is the basic column of the dummy row 0)
      FF_ASSERT(LINEAR, cx > 0);
      int x = cx - 1;

      // Check if basic variable x satisfies the equality in its domain constraints, if there is one.
      auto& eqs = equals_to[x];
      auto it = find_equality(eqs);
      if (it != eqs.end()) {
	const auto& k = trail[*it].value;
	if (sol[x] != k) { // Equality is violated: look for a non-basic variable which is not fixed.
	  found = true;
	  int r = basis->row(cx);

	  FF_ASSERT(LINEAR, r > 0);
	  int y = find_non_basic_non_fixed_variable_in_row(r);
	  if (y != WRONG_INDEX) { // Found a non-basic variable y which is not fixed.

	    int cy = y + 1;
	    FF_ASSERT(LINEAR, basis->row(cy) == WRONG_INDEX);
	    FF_ASSERT(LINEAR, find_equality(equals_to[y]) == equals_to[y].end());
	    // Find the value l for y so that x gets value k, update and swap their roles in the basis.

	    // Since
	    //        a(r, y) *     y   + ... + a(r, x) *      x  = 0
	    // then
	    //        a(r, y) * sol[y]  + ... + a(r, x) *  sol[x] = 0
	    // and
	    //        a(r, y) * l       + ... + a(r, x) *  k      = 0
	    //
	    // Subtracting:
	    //
	    //     a(r, y) * (l - sol[y]) +  a(r, x) * (k - sol[x]) = 0
	    //     a(r, y) * (l - sol[y]) = -a(r, x) * (k - sol[x])
	    //    	     (l - sol[y]) = -a(r, x) * (k - sol[x]) / a(r, y)
	    //    	      l           = -a(r, x) * (k - sol[x]) / a(r, y) + sol[y]

	    Zp l = sol[y] - tableau->value(r, cx) * (k - sol[x]) / tableau->value(r, cy);

	    update(y, l);
	    tableau->pivot(r,  cy);
	    basis  ->pivot(cx, cy);
	  }
	  else { // Found a conflict due to all fixed variables in row r.
	    s.conf_exp.clear();
	    for (auto j = tableau->row_beg(r), ej = tableau->row_end(r); j != ej; j.next(*tableau)) {
	      int cj = tableau->index(j);
	      FF_ASSERT(LINEAR, cj > 0);
	      int xj = cj - 1;  // One of these will be x.
	      auto it = find_equality(equals_to[xj]);
	      FF_ASSERT(LINEAR, it != equals_to[xj].end());
	      const auto& exp = trail[*it].exp;
	      for (auto lit : exp) s.conf_exp.push_back(lit);
	    }
	    res = -s.conf_exp.size();
	  }
	}
      }
      else { // We only need to check disequalities if there is no equality in the domain constraints.

	// Check if basic variable x satisfies the disequalities in its domain constraints.
	auto& disx = diff_from[x];
	auto it = find_disequality(disx, sol[x]);
	if (it != disx.end()) { // A disequality is violated: look for a non-basic variable not fixed.

	  found = true;
	  int r = basis->row(cx);
	  FF_ASSERT(LINEAR, r > 0);
	  int y = find_non_basic_non_fixed_variable_in_row(r);
	  if (y != WRONG_INDEX) { // Found a non-basic variable which is not fixed.
	    FF_ASSERT(LINEAR, basis->row(y + 1) == WRONG_INDEX);
	    FF_ASSERT(LINEAR, find_equality(equals_to[y]) == equals_to[y].end());

	    // Find another value     l for y compatible with the disequalities of y
	    // and which yields a value for x compatible with the disequalities of x.

	    auto& disy = diff_from[y];
	    Zp l = sol[y];
	    do {      // For large primes there should not be a problem of termination.
	      l += 1;
	      update(y, l);
	    }
	    while (find_disequality(disx, sol[x]) != disx.end() or
		   find_disequality(disy, sol[y]) != disy.end());
	  }
	  else { // Found a conflict due to all fixed variables in row r, and a disequality of x.
	    s.conf_exp = trail[*it].exp;
	    for (auto j = tableau->row_beg(r), ej = tableau->row_end(r); j != ej; j.next(*tableau)) {
	      int cj = tableau->index(j);
	      if (cx == cj) continue;
	      FF_ASSERT(LINEAR, cj > 0);
              FF_ASSERT(LINEAR, basis->row(cj) == WRONG_INDEX);
	      int xj = cj - 1;
	      auto it = find_equality(equals_to[xj]);
	      FF_ASSERT(LINEAR, it != equals_to[xj].end());
	      const auto& exp = trail[*it].exp;
	      for (auto lit : exp) s.conf_exp.push_back(lit);
	    }
	    res = -s.conf_exp.size();
	  }
	}
      }
    }
    if (not found and res == UNKNOWN) res = SAT; // If no violating basic variable was found, then satisfied.
  }

  while (res == UNKNOWN) {    // While unknown, i.e., not conflicting and not satisfied, do ...

    FF_ASSERT(LINEAR, ok());

    // Find the largest basic variable whose assigned value violates domain constraints.
    int x = -1;
    bool eq = true;

    for (auto i = basis->beg(), ei = basis->end(); i != ei; i.next(*basis)) {
      int cz = basis->col(i);
      if (cz == 0) continue; // Ignore the dummy column 0 (which is the basic column of the dummy row 0)
      FF_ASSERT(LINEAR, cz > 0);
      int z = cz - 1;

      // Check if basic variable z satisfies the equality in its domain constraints, if there is one.
      auto& eqs = equals_to[z];
      auto it = find_equality(eqs);
      if (it != eqs.end()) {
	const auto& k = trail[*it].value;
	if (sol[z] != k) { // Equality is violated.
	  if (x < z) {
	    x = z;
	    eq = true;
	  }
	}
      }
      else { // We only need to check disequalities if there is no equality in the domain constraints.

	// Check if basic variable z satisfies the disequalities in its domain constraints.
	auto& dis = diff_from[z];
	auto it = find_disequality(dis, sol[z]);
	if (it != dis.end()) { // A disequality is violated.
	  if (x < z) {
	    x = z;
	    eq = false;
	  }
	}
      }
    }

    if (x != -1) {

      int cx = x + 1;
      int r = basis->row(cx);
      FF_ASSERT(LINEAR, r > 0);

      if (eq) {
	const auto& k = trail[*find_equality(equals_to[x])].value;
	FF_ASSERT(LINEAR, sol[x] != k);

	int y = find_largest_non_basic_non_fixed_variable_in_row(r);
	if (y != WRONG_INDEX) { // Found largest non-basic variable y which is not fixed.

	  int cy = y + 1;
	  FF_ASSERT(LINEAR, basis->row(cy) == WRONG_INDEX);
	  FF_ASSERT(LINEAR, find_equality(equals_to[y]) == equals_to[y].end());
	  // Find the value l for y so that x gets value k, update and swap their roles in the basis.

	  // Since
	  //        a(r, y) *     y   + ... + a(r, x) *      x  = 0
	  // then
	  //        a(r, y) * sol[y]  + ... + a(r, x) *  sol[x] = 0
	  // and
	  //        a(r, y) * l       + ... + a(r, x) *  k      = 0
	  //
	  // Subtracting:
	  //
	  //     a(r, y) * (l - sol[y]) +  a(r, x) * (k - sol[x]) = 0
	  //     a(r, y) * (l - sol[y]) = -a(r, x) * (k - sol[x])
	  //    	     (l - sol[y]) = -a(r, x) * (k - sol[x]) / a(r, y)
	  //    	      l           = -a(r, x) * (k - sol[x]) / a(r, y) + sol[y]

	  Zp l = sol[y] - tableau->value(r, cx) * (k - sol[x]) / tableau->value(r, cy);

	  update(y, l);
	  tableau->pivot(r,  cy);
	  basis  ->pivot(cx, cy);
	}
	else { // Found a conflict due to all fixed variables in row r.
	  s.conf_exp.clear();
	  for (auto j = tableau->row_beg(r), ej = tableau->row_end(r); j != ej; j.next(*tableau)) {
	    int cj = tableau->index(j);
	    FF_ASSERT(LINEAR, cj > 0);
	    int xj = cj - 1;  // One of these will be x.
	    auto it = find_equality(equals_to[xj]);
	    FF_ASSERT(LINEAR, it != equals_to[xj].end());
	    const auto& exp = trail[*it].exp;
	    for (auto lit : exp) s.conf_exp.push_back(lit);
	  }
	  res = -s.conf_exp.size();
	}
      }
      else {
	auto& disx = diff_from[x];
	auto it = find_disequality(disx, sol[x]);

	FF_ASSERT(LINEAR, it != disx.end());

	int y = find_largest_non_basic_non_fixed_variable_in_row(r);
	if (y != WRONG_INDEX) { // Found a non-basic variable which is not fixed.
	  FF_ASSERT(LINEAR, basis->row(y + 1) == WRONG_INDEX);
	  FF_ASSERT(LINEAR, find_equality(equals_to[y]) == equals_to[y].end());

	  // Find another value     l for y compatible with the disequalities of y
	  // and which yields a value for x compatible with the disequalities of x.

	  auto& disy = diff_from[y];
	  Zp l = sol[y];
	  do {      // For large primes there should not be a problem of termination.
	    l += 1;
	    update(y, l);
	  }
	  while (find_disequality(disx, sol[x]) != disx.end() or
		 find_disequality(disy, sol[y]) != disy.end());
	}
	else { // Found a conflict due to all fixed variables in row r, and a disequality of x.
	  s.conf_exp = trail[*it].exp;
	  for (auto j = tableau->row_beg(r), ej = tableau->row_end(r); j != ej; j.next(*tableau)) {
	    int cj = tableau->index(j);
	    if (cx == cj) continue;
	    FF_ASSERT(LINEAR, cj > 0);
	    FF_ASSERT(LINEAR, basis->row(cj) == WRONG_INDEX);
	    int xj = cj - 1;
	    auto it = find_equality(equals_to[xj]);
	    FF_ASSERT(LINEAR, it != equals_to[xj].end());
	    const auto& exp = trail[*it].exp;
	    for (auto lit : exp) s.conf_exp.push_back(lit);
	  }
	  res = -s.conf_exp.size();
	}
      }
    }
    else {
      FF_ASSERT(LINEAR, res == UNKNOWN);
      res = SAT; // If no violating basic variable was found, then satisfied.
    }
  }

  FF_ASSERT(LINEAR, ok());

  FF_OUT(LINEAR, "... out of check_consistency_heavy" << endl);

  return res;
}


void Linear_solver::update(int xn, const Zp& val) {

  Zp diff = sol[xn] - val;
  FF_ASSERT(LINEAR, diff != 0);

  int cn = xn + 1;
  for (auto k = tableau->col_beg(cn), ke = tableau->col_end(cn); k != ke; k.next(*tableau)) {
    int r  = tableau->index(k);
    int cb = basis->col(r);
    FF_ASSERT(LINEAR, cb > 0);
    int xb = cb - 1;
    sol[xb] += diff * tableau->value(k) / tableau->value(r, cb);
  }
  sol[xn] = val;
}


void Linear_solver::backtrack(int n) {

  FF_ASSERT(LINEAR, n > 0);

  // Restore trail, domains and counters.
  int s = trail.size();
  int p = n;
  while (p > 0) {
    FF_ASSERT(LINEAR, s > 0);

    while (trail[s-1].valid()) {

      const Domain_constraint& dc = trail[s-1];
      int x = dc.variable;
      if (dc.equal) {
        FF_ASSERT(LINEAR, not equals_to[x].empty());
	FF_ASSERT(LINEAR, equals_to[x].back() == s-1);
	equals_to[x].pop_back();

	if (next_prop >= s) {
	  if (is_original_variable(x)) {
	    for (int i : var2indices[x]) ++idx2cnt[i];
	  }
	  int c = x + 1;  // +1 for the offset of columns in the tableau.
	  for (auto i = initial->col_beg(c), ie = initial->col_end(c); i != ie; i.next(*initial)) {
	    int r = initial->index(i);
	    ++row2cnt[r];
	  }
	}
      }
      else {
        FF_ASSERT(LINEAR, not diff_from[x].empty());
	FF_ASSERT(LINEAR, diff_from[x].back() == s-1);
	diff_from[x].pop_back();
      }
      --s;
      FF_ASSERT(LINEAR, s > 0);
    }
    --s;
    --p;
  }
  trail.resize(s);

  // Restore pointers to next literal to check and next literal to propagate.
  if (next_chck > s) {
    next_chck = s;
    if (next_prop > next_chck) next_prop = next_chck;
  }
}


int Linear_solver::find_non_basic_non_fixed_variable_in_row(int r) {

  int c = basis->col(r);
  for (auto j = tableau->row_beg(r), e = tableau->row_end(r); j != e; j.next(*tableau)) {
    int cj = tableau->index(j);
    if (c == cj) continue;         // Ignore the basic column.
    FF_ASSERT(LINEAR, cj > 0);
    FF_ASSERT(LINEAR, basis->row(cj) == WRONG_INDEX);
    int xj = cj - 1;
    const auto& eqs = equals_to[xj];
    if (find_equality(eqs) == eqs.end()) return xj; // xj is a non-basic variable which is not fixed.
  }
  return -1;
}


int Linear_solver::find_largest_non_basic_non_fixed_variable_in_row(int r) {

  int y = -1;
  int c = basis->col(r);
  for (auto j = tableau->row_beg(r), e = tableau->row_end(r); j != e; j.next(*tableau)) {
    int cj = tableau->index(j);
    if (c == cj) continue;         // Ignore the basic column.
    FF_ASSERT(LINEAR, cj > 0);
    FF_ASSERT(LINEAR, basis->row(cj) == WRONG_INDEX);
    int xj = cj - 1;
    const auto& eqs = equals_to[xj];
    if (find_equality(eqs) == eqs.end()) { // xj is a non-basic variable which is not fixed.
      if (y < xj) y = xj;
    }
  }
  return y;
}


bool Linear_solver::solution_satisfies_equalities() {

  // Skip dummy row.
  for (int r = 1; r < tableau->row_dimension(); ++r) {
    Zp eval = 0;
    for (auto j = tableau->row_beg(r), e = tableau->row_end(r); j != e; j.next(*tableau)) {
      int c = tableau->index(j);
      if (c <= 0) {
	cerr << "Error: found dummy column in a non-dummy row" << endl;
	return false;
      }
      int x = c - 1;
      eval += tableau->value(j) * sol[x];
    }
    if (eval != 0) {
      cerr << "Error: solution evaluates row #" << r << " to non-zero value " << eval << endl;

      for (auto j = tableau->row_beg(r), e = tableau->row_end(r); j != e; j.next(*tableau)) {
	int c = tableau->index(j);
	int x = c - 1;
	cout << " + (" << tableau->value(j) << ") * ["<< to_string(x) << "]";
      }
      cout << endl;
      for (auto j = tableau->row_beg(r), e = tableau->row_end(r); j != e; j.next(*tableau)) {
	int c = tableau->index(j);
	int x = c - 1;
	cerr << "col. # " << c << " ~~> " << sol[x] << endl;
      }
      cout << endl;

      return false;
    }
  }

  for (int r = 1; r < initial->row_dimension(); ++r) {
    Zp eval = 0;
    for (auto j = initial->row_beg(r), e = initial->row_end(r); j != e; j.next(*initial)) {
      int c = initial->index(j);
      if (c <= 0) {
	cerr << "Error: found dummy column in a non-dummy row" << endl;
	return false;
      }
      int x = c - 1;
      eval += initial->value(j) * sol[x];
    }
    if (eval != 0) {
      cerr << "Error: solution evaluates row #" << r << " to non-zero value " << eval << endl;
      return false;
    }
  }

  return true;
}


bool Linear_solver::solution_satisfies_domain_constraints_of_variable(int x) {

  const auto& eqs = equals_to[x];
  auto it = find_equality(eqs);
  if (it != eqs.end() and trail[*it].value != sol[x]) {
    cerr << "Error: solution does not satisfy equality constraint of variable "
         << Context::Variable(x) << "[column " << x+1 << "]" << endl;
    return false;
  }

  const auto& dis = diff_from[x];
  if (find_disequality(dis, sol[x]) != dis.end()) {
    cerr << "Error: solution does not satisfy disequality constraint of variable "
         << Context::Variable(x) << "[column " << x+1 << "]" << endl;
    return false;
  }

  return true;
}


bool Linear_solver::solution_satisfies_domain_constraints_of_non_basic_variables() {

  // Skip dummy column.
  for (int c = 1; c < tableau->col_dimension(); ++c)
    if (basis->row(c) == WRONG_INDEX) {
      int x = c - 1;
      if (not solution_satisfies_domain_constraints_of_variable(x)) return false;
    }

  return true;
}


bool Linear_solver::solution_satisfies_domain_constraints_of_basic_variables() {

  // Skip dummy column.
  for (int c = 1; c < tableau->col_dimension(); ++c)
    if (basis->row(c) != WRONG_INDEX) {
      int x = c - 1;
      if (not solution_satisfies_domain_constraints_of_variable(x)) return false;
    }

  return true;
}


bool Linear_solver::solution_compatible_with_nonlinear_monomials() {

  int n_vars = number_variables();
  int n_orig = s.get_num_vars();
  for (int v = n_orig; v < n_vars; ++v) {
    if (is_monomial_variable(v)) {
      const Monomial& mon = monomial(v);
      Zp eval = 1;
      for (const auto& [u, e] : mon) {
	for (int k = 0; k < e; ++k)
	  eval *= sol[u];
      }
      if (eval != sol[v]) {
        FF_OUT(LINEAR, to_string(v) << " is assigned to " << sol[v]
               << " but should be " << eval << endl);
	return false;
      }
    }
  }
  return true;
}


void Linear_solver::print_solution() {

  cout << endl << "SOLUTION" << endl;
  for (int v = 0; v < s.get_num_vars(); ++v)
    cout << Context::Variable(v) << " ~~> " << sol[v] << endl;
}


int Linear_solver::theoryPropagate(int level) {

  FF_ASSERT(LINEAR, ok());

  int res = 0;
  while (next_prop < next_chck or next_chck < int(trail.size())) {
    while (next_prop < next_chck) {

      FF_ASSERT(LINEAR, ok());

      int idx = next_prop;
      ++next_prop;
      const Domain_constraint& dc = trail[idx];
      if (not dc.valid()) continue;                // Mark of a backtrack point, skip.
      int aux = propagate_domain_constraint(idx);
      if (aux < 0) return aux;
      res += aux;
    }

    while (next_chck < int(trail.size())) {
      int idx = next_chck;
      const Domain_constraint& dc = trail[idx];
      if (dc.valid()) {
	int aux = check_domain_constraint(idx);
	if (aux < 0) return aux;
      }
      ++next_chck;
    }
  }

  int aux = check_consistency_heavy(); // Make a heavy-weight consistency check.
  if (aux < 0) return aux;

  return res;
}



int Linear_solver::
notify_propagation(int x, bool eq, const Zp& k, const vector<Lit>& exp) {

  int res = 0;

  int p = -1;
  const vector<int>& pvars = var2pvars[x];
  for (int q : pvars)
    if (pvar2cns[q] == k) {
      p = q;
      break;
    }
  if (p != -1) {
    Lit plit(p, eq);
    if (s.engine->model.isTrue(~plit)) {    // Conflict with a literal in the assignment.
      return make_conflict_explanation(exp, {~plit});
    }
    else {
      auto it = s.plit2exp.find(~plit);
      if (it != s.plit2exp.end()) {         // Conflict with a propagated literal.
	return make_conflict_explanation(exp, it->second);
      }
      else if (s.plit2exp[plit].empty()) {
	s.plit_stack.push_back(plit);
	s.plit2exp[plit] = exp;
	++res;
      }
    }
  }
  else if (eq) {

    // choose if we want to do this or not
    // WITH FLAG_LINEAR_PROPAGATION FAILS
    bool flag_linear_propagation = false;

    if (flag_linear_propagation){
    TermsDB* DB = s.engine->termsDataBase();
    Polynomial<Zp> x_p; // x as a polynomial
    Term           x_t; // x as a term

    if      (is_original_variable(x)) {
      x_p = Polynomial<Zp>(1, Monomial(x));
      x_t = DB->addTerm(get_var_name(Context::Variable(x)));
    }
    else if (is_monomial_variable(x)) {
      const Monomial& mon = monomial(x);
      x_p = Polynomial<Zp>(1, mon);

      x_t = DB->addNum(1);
      for (const auto& [u, e] : mon)
	for (int k = 0; k < e; ++k)
	  x_t = DB->addTimes(x_t,
			     DB->addTerm(get_var_name(Context::Variable(u))));
    }
    else {
      FF_ASSERT(LINEAR, is_linear_expression_variable(x));
      const Linear_expression& lin = linear_expression(x);
      x_t = DB->addNum(0);
      for (const auto& [y, c] : lin) {
	FF_ASSERT(LINEAR, not is_linear_expression_variable(y));
	Term y_t;
	if      (is_original_variable(y)) {
	  x_p = x_p + Polynomial<Zp>(c, Monomial(y));
	  y_t = DB->addTimes(DB->addNum(c),
			     DB->addTerm(get_var_name(Context::Variable(y))));
	}
	else if (is_monomial_variable(y)) {
	  const Monomial& mon = monomial(y);
	  x_p = x_p + Polynomial<Zp>(c, mon);
	  y_t = DB->addNum(c);
	  for (const auto& [z, e] : mon) {
	    string s = get_var_name(Context::Variable(z));
	    for (int k = 0; k < e; ++k)
	      y_t = DB->addTimes(y_t, DB->addTerm(s));
	  }
	}
	x_t = DB->addPlus(x_t, y_t);
      }
    }

    Monomial one = Monomial();
    Polynomial<Zp> x_minus_k_p;
    if (is_zero(k)) {
      x_minus_k_p = x_p;
    }
    else {
      Polynomial<Zp> mk_p = Polynomial<Zp>(-k, one);
      x_minus_k_p = x_p + mk_p;
    }

    Term k_t = DB->addNum(k);
    Term e_t = DB->addEq(x_t, k_t);

    auto [plit, added] =
      s.engine->arithmeticSolver->abstractTheoryAtom(e_t);

    FF_ASSERT(LINEAR, added);
    FF_ASSERT(LINEAR, s.plit2exp[plit].empty());

    int pvar = s.engine->newSplitVariable(SATSolver::FF_SOLVER);
    FF_ASSERT(SOLVER, Lit(pvar, true) == plit);
    x_minus_k_p.normalize();
    defineNewEquality(pvar, x_minus_k_p);

    //cout << "Adding new equality in linear solver: " << x_minus_k_p <<endl; 

    s.plit_stack.push_back(plit);
    s.plit2exp[plit] = exp;
    ++res;
  }
  }
  return res;
}


int Linear_solver::check_domain_constraint(int idx) {

  const Domain_constraint& dc = trail[idx];

  FF_OUT(LINEAR, "check_domain_constraint #" << idx << ": " << to_string(dc) << endl);

  int            x = dc.variable;
  auto           k = dc.value;
  vector<Lit> lits = dc.exp;

  if (dc.equal) { // Constraint is x == k.

    auto& eqs = equals_to[x];
    auto it = find_equality(eqs);
    if (it != eqs.end()) {
      FF_ASSERT(LINEAR, k != trail[*it].value);
      const auto& exp = trail[*it].exp;
      return make_conflict_explanation(exp, lits);
    }

    // Check if there is a trivial conflict with an already existing disequality.
    auto& dis = diff_from[x];
    auto jt = find_disequality(dis, k);
    if (jt != dis.end()) {
      FF_ASSERT(LINEAR, k == trail[*jt].value);
      const auto& exp = trail[*jt].exp;
      return make_conflict_explanation(exp, lits);
    }

    // Ensure invariant: current solution satisfies domain constraints of non-basic variables.
    int c = x + 1;  // +1 for the offset of columns in the tableau.
    if (basis->row(c) == WRONG_INDEX and sol[x] != k) update(x, k);
  }
  else {          // Constraint is x != k.

    // Check if there is a trivial conflict with an already existing equality.
    auto& eqs = equals_to[x];
    auto it = find_equality(eqs);
    if (it != eqs.end()) {
      const auto&   l = trail[*it].value;
      const auto& exp = trail[*it].exp;
      if (k == l) return make_conflict_explanation(exp, lits); // Conflict with x == k.
      else        return 0;                                    // Redundant.
    }

    // Ensure invariant: current solution satisfies domain constraints of non-basic variables.
    const auto& dis = diff_from[x];
    int c = x + 1;
    if (basis->row(c) == WRONG_INDEX and sol[x] == k) {

      // If there was constraint x == l, then it should be sol[x] == l,
      // thanks to the invariant and that x is non-basic.
      // But then we should have satisfied the above condition: if (k == l) ...
      FF_ASSERT(LINEAR, find_equality(eqs) == eqs.end());

      // Just find a value that satisfies all disequality constraints for x (including x != k).
      Zp l = k + 1;
      while (true) {      // For large primes there should not be a problem of termination.
	auto it = find_disequality(dis, l);
	if (it == dis.end()) break;          // Value l satisfies all disequalities.
	l += 1;
      }
      update(x, l);
    }
  }
  return 0;
}


void eliminate_repeated_literals(vector<Lit>& lits) {
  sort(lits.begin(), lits.end());
  auto it = unique(lits.begin(), lits.end());
  lits.erase(it, lits.end());
}


int Linear_solver::propagate_domain_constraint(int idx) {

  const Domain_constraint& dc = trail[idx];

  FF_OUT(LINEAR, "propagate_domain_constraint #" << idx << ": " << to_string(dc) << endl);

  int            x = dc.variable;
  auto           k = dc.value;
  vector<Lit> lits = dc.exp;

  int res = 0;

  if (dc.equal) {

    FF_ASSERT(LINEAR, *find_equality(equals_to[x]) == idx);

    // Equality x == k propagates disequalities x != l for all l != k.
    const vector<int>& pvars = var2pvars[x];
    for (int q : pvars) {
      if (res < 0)          continue;
      if (pvar2cns[q] == k) continue;
      Lit plit(q, false);
      if (s.engine->model.isTrue(~plit)) { // Conflict with a literal in the assignment.
	s.conf_exp = lits;
	s.conf_exp.push_back(~plit);
	res = -s.conf_exp.size();
      }
      else {
	auto it = s.plit2exp.find(~plit);
	if (it != s.plit2exp.end()) {         // Conflict with a propagated literal.
	  s.conf_exp = lits;
	  for (Lit lit : it->second) s.conf_exp.push_back(lit);
	  res = -s.conf_exp.size();
	}
	else if (s.plit2exp[plit].empty()) {
	  s.plit_stack.push_back(plit);
	  s.plit2exp[plit] = lits;
	  FF_ASSERT(LINEAR, res >= 0);
	  ++res;
	}
      }
    }

    // A monomial gets a fixed value if all its variables are fixed (or at least one is fixed to zero).
    if (is_original_variable(x)) {
      for (int i : var2indices[x]) {
	--idx2cnt[i];
	if (res < 0) continue;
	if (idx2cnt[i] == 0 or is_zero(k)) {
	  vector<Lit> exp;
	  const Monomial& mon = idx2mon[i];
	  Zp eval = 0;
	  if (k == 0) {
	    exp = lits;
	  }
	  else {
	    eval = 1;
	    for (const auto& [z, e] : mon) {
	      const auto& eqs = equals_to[z];
	      auto it = find_equality(eqs);
	      FF_ASSERT(LINEAR, it != eqs.end());
	      const Zp& v = trail[*it].value;
	      if (v == 0) {
		eval = 0;
		exp = trail[*it].exp;
		break;
	      }
	      else {
		for (int j = 0; j < e; ++j)
		  eval *= v;
		for (Lit lit : trail[*it].exp)
		  exp.push_back(lit);
	      }
	    }
	    eliminate_repeated_literals(exp);
	  }

	  int y = s.get_num_vars() + idx2rnk[i];
	  FF_ASSERT(LINEAR, monomial(y) == mon);
	  if (assert_equality(y, eval, exp)) {

#if FF_PRINT
            FF_OUT(LINEAR, mon << " is now fixed to value " << eval << " due to literal(s)");
            for (Lit lit : exp) FF_OUT(LINEAR, " " << lit);
            FF_OUT(LINEAR, endl);
#endif
	    int aux = notify_propagation(y, true, eval, exp);
	    if (aux < 0) res  = aux;
	    else         res += aux;
	  }
	}
      }
    }

    // Check if equality v == k propagates an equality using the rows of the initial tableau.

    int c = x + 1;  // +1 for the offset of columns in the tableau.

    for (auto i = initial->col_beg(c), ie = initial->col_end(c); i != ie; i.next(*initial)) {
      int r = initial->index(i);
      --row2cnt[r];
      if (res < 0) continue;
      if (row2cnt[r] == 1) {
	Zp eval = 0;
	Zp coef = 0;
	int y = -1;
	vector<Lit> exp;
	for (auto j = initial->row_beg(r), je = initial->row_end(r); j != je; j.next(*initial)) {
	  int cz = initial->index(j);
	  int z = cz - 1;
	  auto it = find_equality(equals_to[z]);
	  if (it == equals_to[z].end()) {
	    FF_ASSERT(LINEAR, y == -1);
	    y = z;
	    coef = initial->value(j);
	  }
	  else {
	    eval += initial->value(j) * trail[*it].value;
	    for (Lit lit : trail[*it].exp)
	      exp.push_back(lit);
	  }
	}

	if (y == -1) {
	  if (eval != 0) {
	    s.conf_exp = exp;
	    res = -s.conf_exp.size();
	  }
	  continue;
	}

	FF_ASSERT(LINEAR, coef !=  0);
	eval = -eval / coef;

	eliminate_repeated_literals(exp);

	if (assert_equality(y, eval, exp)) {

#if FF_PRINT
          FF_OUT(LINEAR, to_string(y) << " is now fixed to value " << eval << " due to literal(s)");
          for (Lit lit : exp) FF_OUT(LINEAR, " " << lit);
          FF_OUT(LINEAR, endl);
#endif

	  int aux = notify_propagation(y, true, eval, exp);
	  if (aux < 0) res  = aux;
	  else         res += aux;
	}
      }
    }
  }
  else {
    if (k == 0 and is_monomial_variable(x)) {
      const auto& mon = monomial(x);
      for (const auto& [y, e] : mon) {

	if (res < 0) continue;

	if (assert_disequality(y, 0, lits)) {
	  int aux = notify_propagation(y, false, 0, lits);
	  if (aux < 0) res  = aux;
	  else         res += aux;
	}
      }
    }
  }
  return res;
}

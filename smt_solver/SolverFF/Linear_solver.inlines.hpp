#ifndef FF_LINEAR_SOLVER_INLINES_HPP
#define FF_LINEAR_SOLVER_INLINES_HPP

#include "F_matrix.inlines.hpp"
#include "C_matrix.inlines.hpp"
#include "Basis.inlines.hpp"
#include "Solver.defs.hpp"
#include "Linear_solver.defs.hpp"

namespace FF {


inline ostream& operator << (ostream& out, const Linear_expression& lin) {
  for (const auto& [ffvar, coe] : lin) {
    out << " + (" << coe << ") " << Context::Variable(ffvar);
  }
  return out;
}


inline Linear_solver::Linear_solver(Solver& s) :
  s(s), tableau(NULL), basis(NULL), next_chck(0), next_prop(0), initial(NULL), row2cnt(1) { }


inline vector<int>::const_iterator
Linear_solver::find_equality(const vector<int>& eqs) {

  auto checked = [&](int i) { return i < next_chck; };
  return find_if(eqs.begin(), eqs.end(), checked);
}


inline vector<int>::const_iterator
Linear_solver::find_disequality(const vector<int>& dis, const Zp& k) {

  auto is_k = [&](int i) {
    return i < next_chck and trail[i].value == k;
  };
  
  return find_if(dis.begin(), dis.end(), is_k);
}


inline int Linear_solver::make_conflict_explanation(const vector<Lit>& lits, const vector<Lit>& others) {
  s.conf_exp = lits;
  for (Lit l : others) s.conf_exp.push_back(l);
  return -s.conf_exp.size();
}


inline void Linear_solver::setBTPoint() {
  trail.push_back( Domain_constraint() );
}


inline int Linear_solver::number_variables() {
  return s.get_num_vars() + int(rnk2idx_pos.size());
}


inline bool Linear_solver::is_original_variable(int v) {
  return v < s.get_num_vars();
}


inline bool Linear_solver::is_monomial_variable(int v) {
  if (v < s.get_num_vars()) return false;
  int rnk = v - s.get_num_vars();
  return rnk2idx_pos[rnk].second;
}


inline bool Linear_solver::is_linear_expression_variable(int v) {
  if (v < s.get_num_vars()) return false;
  int rnk = v - s.get_num_vars();
  return not(rnk2idx_pos[rnk].second);
}


inline const Monomial& Linear_solver::monomial(int v) {
  FF_ASSERT(LINEAR, is_monomial_variable(v));
  int rnk = v - s.get_num_vars();
  return idx2mon[ rnk2idx_pos[rnk].first ];
}


inline const Linear_expression& Linear_solver::linear_expression(int v) {
  FF_ASSERT(LINEAR, is_linear_expression_variable(v));
  int rnk = v - s.get_num_vars();
  return pos2lin[ rnk2idx_pos[rnk].first ];
}


inline string Linear_solver::to_string(int v) {
  ostringstream out;
  if      (is_original_variable(v)) out << Context::Variable(v);
  else if (is_monomial_variable(v)) out << monomial(v);
  else {
    bool first = true;
    for (const auto& [ffvar, coe] : linear_expression(v)) {
      if (not first) out << " + ";
      if (coe == 1)  out               << to_string(ffvar);
      else           out << coe << " " << to_string(ffvar);
      first = false;
    }
  }
  return out.str();
}


inline string Linear_solver::to_string(const Domain_constraint& dc) {

  ostringstream out;

  string sep(4, ' ');

  out << to_string(dc.variable)
      << (dc.equal ? " == " : " != ")
      << dc.value
      << sep
      << " <- ";

  for (Lit lit : dc.exp)
    out << s.to_string(lit) << "; ";

  return out.str();
}


inline void Linear_solver::setTrue(Lit lit) {

  int pvar = var(lit);

  const auto& x = pvar2var[pvar];
  const auto& k = pvar2cns[pvar];

  if (isPositive(lit)) assert_equality   (x, k, vector<Lit>{lit});
  else                 assert_disequality(x, k, vector<Lit>{lit});
}


inline bool
Linear_solver::assert_equality   (int x, const Zp& k, const vector<Lit>& exp) {
  auto& eqs = equals_to[x];
  auto is_k = [&](int i) { return trail[i].value == k; };
  auto it = find_if(eqs.begin(), eqs.end(), is_k);
  if (it != eqs.end()) return false; // Redundant.
  eqs.push_back(trail.size());
  Domain_constraint c(x, true, k, exp);
  trail.push_back(c);
  return true;
}


inline bool
Linear_solver::assert_disequality(int x, const Zp& k, const vector<Lit>& exp) {
  auto& dis = diff_from[x];
  auto is_k = [&](int i) { return trail[i].value == k; };
  auto it = find_if(dis.begin(), dis.end(), is_k);
  if (it != dis.end()) return false; // Redundant.
  dis.push_back(trail.size());
  Domain_constraint c(x, false, k, exp);
  trail.push_back(c);
  return true;
}



} // namespace FF

#endif // FF_LINEAR_SOLVER_INLINES_HPP

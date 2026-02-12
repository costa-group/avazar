#include "Solver.inlines.hpp"
#include "../termsDB/termsDB.defs.hpp"
#include "../termsDB/termsDB.inlines.hpp"
#include "../dpllx/SATSolver.h"
#include "../arithmeticSolver.defs.hpp"
#include "../SMTLIBSolver.defs.hpp"
#include <ctime>

using namespace FF;

// MODE no_la -> uses the deduction rules since the beginning, does not use la logic
// if no MODE no_la -> uses LA solver, the deductions are only applied in leaf nodes
// MODE just_non_linear -> does not perform deductions or LA solver, just non linear


struct ConstantsResult{
  bool isValid;
  int signal;
  Zp value;
};

ConstantsResult get_constant_variables(const Polynomial<Zp>& pol){
  std::ostringstream polynomialStream;

  //std::cout << "Checking if Polynomial is constant: " << pol << std::endl;
  ConstantsResult result;
  result.isValid = false;
  // Case x = 0
  if (pol.size() == 1){
    auto [mon, coef] = *pol.begin();
    if (coef != 0 && mon.size() == 1){
      auto [u, e] = *mon.begin();
      result.isValid = true;
      result.signal = u;
      result.value = 0;
      //std::cout << "Constant signal " << u << " value -> 0" << std::endl;
    }
  }
  // Case x = value
  else if(pol.size() == 2){
    bool found_x = false;
    int x;
    Zp coef_x;
    bool found_value = false;
    Zp value;
    for (const auto& [mon, coef] : pol) {
      if (coef != 0 && mon.size() == 1){
        auto [u, e] = *mon.begin();
        if (e == 1){
          found_x = true;
          coef_x = coef;
          x = u;
        } else{
          return result;
        }
      } else if (mon.size() == 0){
        found_value = true;
        value = coef;
      } else{
        return result;
      }
    }
    if (found_value && found_x){
      result.isValid = true;
      result.signal = x;
      result.value = -value/coef_x;
      //std::cout << "Constant signal " << u << "value -> " << result.value << std::endl;
    }
  }
  return result;

}

/////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////


bool update_bounds_signal(
			  Bounds &bounds,
			  int signal,
			  mpz_class min,
			  mpz_class max,
			  set<Var> deduced_min,
			  set<Var> deduced_max

			  ){
  bool updated = false;

  BoundsInfo new_bounds;

  if (bounds.count(signal) > 0){
    //return false;
    //cout << "Updating the bounds of signal already studied" << endl;
    auto [prev_min, prev_max, prev_min_deduced_from, prev_max_deduced_from] = bounds[signal];
    if(prev_min < min){
      new_bounds.min = min;
      new_bounds.min_deduced_from = deduced_min;

      updated = true;
    } else{
      new_bounds.min = prev_min;
      new_bounds.min_deduced_from = prev_min_deduced_from;
    }

    if(prev_max > max){
      new_bounds.max = max;
      new_bounds.max_deduced_from = deduced_max;

      updated = true;
    } else{
      new_bounds.max = prev_max;
      new_bounds.max_deduced_from = prev_max_deduced_from;

    }

    if (updated)
      bounds[signal] = new_bounds;
  } else{
    new_bounds.min = min;
    new_bounds.max = max;
    new_bounds.min_deduced_from = deduced_min;
    new_bounds.max_deduced_from = deduced_max;

    updated = true;

    bounds[signal] = new_bounds;
  }
  return updated;
}

bool detect_bounds_initial(const Polynomial<Zp> &b, Bounds &bounds, Var v, Square_rooter &rooter){
  bool updated = false;

  std::set<unsigned int> s1 = {v}, s2 = {v};

  //cout << "Considering polynomial " << b << endl;
  //cout << "ROOTS: " << b.known_roots << endl;
  auto [is_binary, signal] = is_binary_constraint(b);
  if (is_binary){
    updated = update_bounds_signal(bounds, signal, 0, 1, s1, s2);

  } else{
    auto [is_constant, signal, value] = get_constant_variables(b);
    if (is_constant && is_positive(value)){
      updated = update_bounds_signal(bounds, signal, value.get_v(), value.get_v(), s1, s2);
    } else if (b.known_roots){
      bool is_valid = true;
      bool found_first = false;
      int defined_signal;
      mpz_class max_value, min_value;
      //cout << "It has known roots" << endl;
      for (auto [signal, value]: b.roots){
        //cout << "Root:" << signal << "-> "<< value << endl;
        if (!is_positive(value)){
          is_valid = false;
          break;
        }

        if (!found_first){
          defined_signal = signal;
          min_value = value.get_v();
          max_value = value.get_v();
          found_first = true;
        } else{
          if (defined_signal == signal){
            if (value.get_v() > max_value) max_value = value.get_v();
            if (value.get_v() < min_value) min_value = value.get_v();
          } else{
            is_valid = false;
          }
        }
      }

      if (is_valid && found_first){
        //cout << "Updating bounds with " << min_value << " " << max_value << endl;
        updated = update_bounds_signal(bounds, defined_signal, min_value, max_value, s1, s2);
      }


    } else{
      // using roots calculator, case all linears define possible value of same signal
      // apply only if the polynomial includes a single signal
      bool apply_roots = true;
      set<int> signals = get_signals(b);
      if (apply_roots && signals.size() == 1){
        int defined_signal = *begin(signals);
        // no roots now
        Propagator prop(rooter, b);

        // Compute the roots of the polynomial and add linear constraints if found
        vector< vector< pair<Polynomial<Zp>, bool> > > res = prop.result();
        // A vector of class pair<Polynomial<Zp>,bool>   means their disjunction.
        // A vector of vector<pair<Polynomial<Zp>,bool>> means their conjunction.
        for (const vector< pair<Polynomial<Zp>, bool> >& v : res) {
          // For each one of the elements of the conjunction add a new clause
          bool is_valid = true;
          bool found_first = false;
          mpz_class max_value, min_value;
          for (const auto& [q, e] : v) {
            // only if it is possitve
            if (e){
              // in case is a constant and positive            
              auto [is_constant, signal, value] = get_constant_variables(q);
              assert(signal == defined_signal);
              if (is_constant &&  is_positive(value)){
                if (!found_first){
                  max_value = value.get_v();
                  min_value = value.get_v();
                  found_first = true;
                } else{
                  if (value.get_v() > max_value) max_value = value.get_v();
                  if (value.get_v() < min_value) min_value = value.get_v();
                }
              } else{
                is_valid = false;
                break;
              }
            } else{
              is_valid = false;
              break;
            }
          } 
          if (is_valid && found_first){
            updated = update_bounds_signal(bounds, defined_signal, min_value, max_value, s1, s2);
          }
        }
      }
    }
  }
  return updated;
}

pair<mpz_class, set<Var>> get_max_value_monomial(const Monomial &b, Bounds &bounds){
  mpz_class result = 1;
  set<Var> deduced_from;
  for (auto [signal, exp]: b){
    if(bounds.count(signal) > 0){
      auto [min, max, min_deduced, max_deduced] = bounds.at(signal);
      for (int i = 0; i < exp; i++){
        result = max * result;
      }
      deduced_from.merge(max_deduced);
    } else{
      mpz_class max = mpz_class(prime) - 1;
      for (int i = 0; i < exp; i++){
        result = max * result;
      }
    }
  }
  // if too big --> return false?, too big to compute?
  return {result, deduced_from};
}

pair<mpz_class, set<Var>> get_min_value_monomial(const Monomial &b, Bounds &bounds){
  mpz_class result = 1;
  set<Var> deduced_from;

  for (auto [signal, exp]: b){
    if(bounds.count(signal) > 0){
      auto [min, max, min_deduced, max_deduced] = bounds[signal];

      for (int i = 0; i < exp; i++){
        result = min * result;
      }
      deduced_from.merge(min_deduced);

    } else{
      result = 0;
    }
  }
  return {result, deduced_from};
}


pair<mpz_class, set<Var>> get_max_value_polynomial(const Polynomial<Zp> &b, Bounds &bounds){
  mpz_class result = 0;
  set<Var> deduced_from;
  for (auto [monomial, coef]: b){
    if (is_positive(coef)){

      auto [max, deduced] = get_max_value_monomial(monomial, bounds);
      result += coef.get_v() * max;
      deduced_from.merge(deduced);

    } else{

      mpz_class neg_monomial = coef.get_v();


      auto [min, deduced] = get_min_value_monomial(monomial, bounds);


      result += neg_monomial * min;
      deduced_from.merge(deduced);
    }
  }
  return {result, deduced_from};
}

pair<mpz_class, set<Var>> get_min_value_polynomial(const Polynomial<Zp> &b, Bounds &bounds){
  mpz_class result = 0;
  set<Var> deduced_from;

  for (auto [monomial, coef]: b){
    if (is_positive(coef)){
      auto [min, deduced] = get_min_value_monomial(monomial, bounds);
      result += coef.get_v() * min;
      deduced_from.merge(deduced);
    } else{
      mpz_class neg_monomial = coef.get_v();
      auto [max, deduced] = get_max_value_monomial(monomial, bounds);
      result += neg_monomial * max;
      deduced_from.merge(deduced);
    }
  }
  return {result, deduced_from};
}

bool check_same_round(mpz_class &v1, mpz_class &v2, mpz_class &p){
  bool same_sign = (v1 >= 0 && v2 >= 0) || (v1 < 0 && v2 < 0);
  return (v1 / p == v2 / p) && same_sign;
}



bool compute_bounds_signal(const Polynomial<Zp> &b, Bounds &bounds, int signal, Var v){

  mpz_class p = mpz_class(prime);
  bool updated = false;

  auto [with_signal, without_signal] = partition(b, signal);

  auto [max_poly, deduced_max] = get_max_value_polynomial(without_signal, bounds);
  auto [min_poly, deduced_min] = get_min_value_polynomial(without_signal, bounds);


  // add the polynomial from which we are extracting the info
  set<Var> deduced = {v};
  deduced_max.insert(v);
  deduced_min.insert(v);

  if (is_one(with_signal)){
    // The min depends on the values of the max, the min on the values of the max
    // deduced interchange
    mpz_class aux_min = -max_poly;
    mpz_class aux_max = -min_poly;

    if (check_same_round(aux_min, aux_max, p)){
      updated = update_bounds_signal(bounds, signal, aux_min % p, aux_max%p, deduced_max, deduced_min);
    }
  } else if (is_minus_one(with_signal)){
    if (check_same_round(min_poly, max_poly, p)){
      updated =  update_bounds_signal(bounds, signal,  min_poly% p, max_poly%p, deduced_min, deduced_max);
    }

  } else{
    cout << "ERROR" <<endl;
  }

  return updated;
}

/*
  void Solver::prepare_LA_check(LA::Solver & la_solver) {
  std::cout << "preparing LA checker ..." << std::endl;
  int curProposition = 2;
  vector<Lit> la_literals;
  TermsDB* dbla = engine->termsDataBase();
  //la_solver.print_constraints(std::cout);
  for (auto[signal, info]: bounds){
  //std::cout << "Current proposition "<< curProposition << std::endl;
  Term term_signal = dbla->addTerm(get_var_name(Context::Variable(signal)));
  Term lb = dbla->addGe(term_signal,dbla->addNum(info.min));
  //std::cout << "Term: " << dbla->term2string(lb) << std::endl;
  Lit llb = la_solver.abstractLiteral(*dbla,lb,curProposition++);
  la_literals.push_back(llb);
  //std::cout << "Lit: " << llb << " ; Cons: " << la_solver.cons_db.constraint(llb) << std::endl;
  Term ub = dbla->addLe(term_signal,dbla->addNum(info.max));
  //std::cout << "Term: " << dbla->term2string(ub) << std::endl;
  // std::cout << "before abstarct" << std::endl;
  Lit lub = la_solver.abstractLiteral(*dbla,ub,curProposition++);
  la_literals.push_back(lub);
  //std::cout << "Lit: " << lub << " ; Cons: " << la_solver.cons_db.constraint(lub) << std::endl;
  //std::cout << "after setting" << std::endl;
  //    for (Var v: info.min_deduced_from){
  // this->getPolynomial(v);
  //}
  //for (Var v: info.max_deduced_from){
  //this->getPolynomial(v);
  //
  //la_solver.print_constraints(std::cout);
  }
  //std::cout << "end bounds" << std::endl;
  //la_solver.print_constraints(std::cout);
  for (auto[lit, deduced_from]: not_overflowing_constraints){
  //std::cout << "Current proposition "<< curProposition << std::endl;
  auto p = var(lit);
  bool is_pos = lit.isPositive();
  if (is_pos) {
  Term poly = engine->arithmeticSolver->termOfPropositionalVariable(p);
  FF_ASSERT(SOLVER, dbla->isEq(poly));
  FF_ASSERT(SOLVER, dbla->arity(poly) == 2);
  FF_ASSERT(SOLVER, dbla->term2string(dbla->ithChild(poly,1)) == dbla->term2string(dbla->addNum(0)));
  Term poly_exp = dbla->ithChild(poly,0);
  Term polyLeq = dbla->addLe(poly_exp,dbla->addNum(0));
  //std::cout << "Term: " << dbla->term2string(polyLeq) << std::endl;
  Lit lpol = la_solver.abstractLiteral(*dbla,polyLeq,curProposition++);
  la_literals.push_back(lpol);
  //std::cout << "Lit: " << lpol << " ; Cons: " << la_solver.cons_db.constraint(lpol) << std::endl;
  Term polyGeq = dbla->addGe(poly_exp,dbla->addNum(0));
  //std::cout << "Term: " << dbla->term2string(polyGeq) << std::endl;
  Lit gpol = la_solver.abstractLiteral(*dbla,polyGeq,curProposition++);
  la_literals.push_back(gpol);
  //std::cout << "Lit: "<<  gpol << " ; Cons: " << la_solver.cons_db.constraint(gpol) << std::endl;
  }
  }
  //std::cout << "end bounded lits" << std::endl;
  //la_solver.print_constraints(std::cout);
  la_solver.initializeAfterParsing();
  //la_solver.setBTPoint();
  for (Lit l: la_literals){
  la_solver.setTrue(l);
  }
  }
*/


int Solver::build_FF_conflict_from_LA(z3::solver &s){
  using namespace z3;
  set<Var> explain;
  set<Lit> explain_neg;
  // cout << "LA explain: " << endl;
  auto lcore = s.unsat_core();
  for (expr  p: lcore) {
    // cout << "is prop: " << p.decl().name().str() << endl;
    for (Var v:  Z3FFLiteralRelation[p.decl().name().str()]) {
      explain.insert(v);
    }
    if (Z3FFnegativeLiterals.find(p.decl().name().str()) != Z3FFnegativeLiterals.end()) {
      explain_neg.insert(Z3FFnegativeLiterals[p.decl().name().str()]);
    }
  }
  conf_exp.clear();
  for (Var v: explain) {
    conf_exp.push_back(Lit(v,true));
    FF_ASSERT(LIA, engine->isTrueLiteral(conf_exp.back()));
    // cout << to_string(Lit(v,true))<< endl;
  }
  for (Lit l: explain_neg) {
    conf_exp.push_back(l);
    FF_ASSERT(LIA, engine->isTrueLiteral(conf_exp.back()));
    // cout << to_string(l)<< endl;
  }
  return -conf_exp.size();
}

z3::expr term2z3expression(TermsDB * db, Term t, z3::context &c) {
  using namespace z3;
  if (db->isNumeral(t)) {
    //std::cout << "Num: " << db->term2string(t) << std::endl;
    return c.int_val(db->term2string(t).c_str());
  }
  if (!db->arity(t)){// Variable
    //std::cout << "Var: " << db->term2string(t) << std::endl;
    return c.int_const(db->topSymbol(t).c_str());
  }
  FF_ASSERT(LIA, db->isTimes(t) || db->isPlus(t)  || db->isUnaryMinus(t) || db->isBinaryMinus(t));
  FF_ASSERT(LIA, db->arity(t) >= 1);
  expr e0 =  term2z3expression(db,db->ithChild(t, 0),c);
  if (db->isUnaryMinus(t)){
    return -e0;
  }
  FF_ASSERT(LIA, db->arity(t) >= 2);
  if (db->isTimes(t)){
    FF_ASSERT(LIA, db->arity(t) == 2);
    expr e1 =  term2z3expression(db,db->ithChild(t, 1),c);
    return e0 * e1;
  }
  if (db->isPlus(t)){
    expr e = e0;
    for (uint i = 1; i < db->arity(t); i++) {
      e = e + term2z3expression(db,db->ithChild(t, i),c);
    }
    return e;
  }
  if (db->isBinaryMinus(t)){
    expr e = e0;
    for (uint i = 1; i < db->arity(t); i++) {
      e = e - term2z3expression(db,db->ithChild(t, i),c);
    }
    return e;
  }
}

void Solver::prepare_LA_check(z3::context &c, z3::solver &s, bool incremental) {
  using namespace z3;
  std::set<uint> sadded;
  Z3FFLiteralRelation.clear();
  Z3FFnegativeLiterals.clear();
  uint overflowing_added = 0;
  std::cout << "preparing LA checker ..." << std::endl;
  uint ubcount = 0;
  uint lbcount = 0;
  uint ecount = 0;
  uint ncount = 0;
  if (incremental) {
    expr_vector added = s.assertions();
    // std::cout << "Added:" << std::endl;
    for (auto e: added) {
      // std::cout << e << " ; " << e.id() << std::endl;
      sadded.insert(e.arg(1).id());
    }
  }
  TermsDB* dbla = engine->termsDataBase();
  for (auto[signal, info]: bounds){
    // std::cout << "Bound signal: " << signal << " , " << info.min << " , " << info.max << std::endl;
    expr term_signal = c.int_const(get_var_name(Context::Variable(signal)).c_str());
    expr lb = term_signal >= c.int_val(info.min.get_str().c_str());
    // std::string proplb = "lb" + std::to_string(lbcount++);
    std::string proplb = "lb" + std::to_string(signal) + "_" + info.min.get_str();
    //    if (incremental) {
      //std::cout << "Checking " << lb <<  " with " << lb.id() << std::endl;
    if (sadded.find(lb.id()) == sadded.end()) {
      // std::cout << "Bound added: " << lb <<  " with " << lb.id() << std::endl;
        s.add(lb,proplb.c_str());
        sadded.insert(lb.id()); //new to avoid repeated
      }
    /*} else {
      std::cout << "Bound added: " << lb <<  " with " << lb.id() << std::endl;
      s.add(lb,proplb.c_str());
      sadded.insert(lb.id());
      }*/
    Z3FFLiteralRelation[proplb.c_str()] = info.min_deduced_from;
    expr ub = term_signal <= c.int_val(info.max.get_str().c_str());
    //std::cout << "Term: " << ub << std::endl;
    //std::string propub = "ub" + std::to_string(ubcount++);
    std::string propub = "ub" + std::to_string(signal) + "_" + info.max.get_str();
    //  if (incremental) {
      // std::cout << "Checking " << ub <<  " with " << ub.id() << std::endl;
    if (sadded.find(ub.id()) == sadded.end()) {
        //std::cout << "Bound added: " << ub <<  " with " << ub.id() << std::endl;
        s.add(ub,propub.c_str());
        sadded.insert(ub.id());
      }
    /*} else {
      std::cout << "Bound added: " << ub <<  " with " << ub.id() << std::endl;
      s.add(ub,propub.c_str());
      sadded.insert(ub.id());
      }*/
    Z3FFLiteralRelation[propub.c_str()] = info.max_deduced_from;
  }
  // std::cout << "end bounds" << std::endl;

  for (auto[lit, deduced_from]: not_overflowing_constraints){
    auto p = var(lit);
    bool is_pos = lit.isPositive();
    Term poly = engine->arithmeticSolver->termOfPropositionalVariable(p);
    FF_ASSERT(LIA, dbla->isEq(poly));
    FF_ASSERT(LIA, dbla->arity(poly) == 2);
    //FF_ASSERT(LIA, dbla->term2string(dbla->ithChild(poly,1)) == dbla->term2string(dbla->addNum(0)));
    expr poly_exp_0 = term2z3expression(dbla,dbla->ithChild(poly,0),c);
    expr poly_exp_1 = term2z3expression(dbla,dbla->ithChild(poly,1),c);

    if (is_pos) {
      //std::cout << "Positive: " << dbla->term2string(poly) << std::endl;
      expr polyLeq = poly_exp_0 <= poly_exp_1;
      expr polyGeq = poly_exp_0 >= poly_exp_1;
      //expr polyEq = poly_exp_0 == poly_exp_1;
      // std::string propeq = "eq" + std::to_string(ecount++);
      std::string propeq = "eq" + std::to_string(poly.ptr()->code());
      expr pe = polyLeq && polyGeq;
      //if (incremental) {
        // std::cout << "Checking " << pe <<  " with " << pe.id() << std::endl;
      if (sadded.find(pe.id()) == sadded.end()) {
        // std::cout << "Positive added " << pe <<  " with " << pe.id() << std::endl;
        s.add(pe,propeq.c_str());
        sadded.insert(pe.id());
        // if (sadded.find(polyEq.id()) == sadded.end()) {
        // std::cout << "Positive NO added " << polyEq <<  " with " << polyEq.id() << std::endl;
        // s.add(polyEq,propeq.c_str());
        // sadded.insert(polyEq.id());
      }
      /*} else {
        std::cout << "Positive added " << pe <<  " with " << pe.id() << std::endl;
        s.add(pe,propeq.c_str());
        sadded.insert(pe.id());
        }*/
      Z3FFLiteralRelation[propeq.c_str()] = deduced_from;
      Z3FFLiteralRelation[propeq.c_str()].insert(p);
      // cout << propeq.c_str() << ": ";
      // for (Var v:Z3FFLiteralRelation[propeq.c_str()]) {
      //   cout << v << ", ";
      // }
      // cout <<endl;
    } else {
      //std::cout << "Negative: " << dbla->term2string(poly) << std::endl;
      expr polyLt = poly_exp_0 < poly_exp_1;
      expr polyGt = poly_exp_0 > poly_exp_1;
      //expr polyNe = poly_exp_0 != poly_exp_1;
      // std::string propneq = "neq" + std::to_string(ncount++);
      std::string propneq = "neq" + std::to_string(poly.ptr()->code());
      expr pn = polyLt || polyGt;
      // if (incremental) {
        // std::cout << "Checking " << pn <<  " with " << pn.id() << std::endl;
      if (sadded.find(pn.id()) == sadded.end()) {
        // std::cout << "Negative added " << pn <<  " with " << pn.id() << std::endl;
        s.add(pn, propneq.c_str());
        sadded.insert(pn.id());
      // if (sadded.find(polyNe.id()) == sadded.end()) {
          // std::cout << "Negative added " << polyNe <<  " with " << polyNe.id() << std::endl;
          // s.add(polyNe, propneq.c_str());
          // sadded.insert(polyNe.id());
        } 
      /*} else {
        std::cout << "Negative added " << pn <<  " with " << pn.id() << std::endl;
        s.add(pn, propneq.c_str());
        sadded.insert(pn.id());
      }*/
      Z3FFLiteralRelation[propneq.c_str()] = deduced_from;
      Z3FFnegativeLiterals[propneq.c_str()] = lit;
      // cout << propneq.c_str() << ": ";
      // for (Var v:deduced_from) {
      //   cout << v << ", ";
      // }
      // cout << Z3FFnegativeLiterals[propneq.c_str()] <<endl;
    }
    //std::cout << "end bounded lits" << std::endl;
  }
  for (auto[poly, deduced_from]: deduced_not_overflowing){
    //std::cout << "Current proposition "<< curProposition << std::endl;
    Term poly_term = generate_term_from_polynomial(poly);
    // std::cout << "Positive NO: " << dbla->term2string(poly_term) << std::endl;
    
    FF_ASSERT(LIA, dbla->isEq(poly_term));
    FF_ASSERT(LIA, dbla->arity(poly_term) == 2);
    //FF_ASSERT(LIA, dbla->term2string(dbla->ithChild(poly,1)) == dbla->term2string(dbla->addNum(0)));
    expr poly_exp_0 = term2z3expression(dbla,dbla->ithChild(poly_term,0),c);
    expr poly_exp_1 = term2z3expression(dbla,dbla->ithChild(poly_term,1),c);

    expr polyLeq = poly_exp_0 <= poly_exp_1;
    expr polyGeq = poly_exp_0 >= poly_exp_1;
    //expr polyEq = poly_exp_0 == poly_exp_1;
    // std::string propeq = "eq" + std::to_string(ecount++);
    std::string propeq = "eq" + std::to_string(poly_term.ptr()->code());
    expr pe = polyLeq && polyGeq;
    //if (incremental) {
      // std::cout << "Checking " << pe <<  " with " << pe.id() << std::endl;
    if (sadded.find(pe.id()) == sadded.end()) {
      // std::cout << "Positive NO added " << pe <<  " with " << pe.id() << std::endl;
      s.add(pe,propeq.c_str());
      sadded.insert(pe.id());
    // if (sadded.find(polyEq.id()) == sadded.end()) {
        // std::cout << "Positive NO added " << polyEq <<  " with " << polyEq.id() << std::endl;
        // s.add(polyEq,propeq.c_str());
        // sadded.insert(polyEq.id());
        // std::cout << "Positive: " << dbla->term2string(poly_term) << std::endl;
        //std::cout << "end bounded lits" << std::endl;
      }
      /*} else {
      std::cout << "Positive NO added " << pe <<  " with " << pe.id() << std::endl;
      s.add(pe,propeq.c_str());
      sadded.insert(pe.id());
      //std::cout << "end bounded lits" << std::endl;
    }*/      
    Z3FFLiteralRelation[propeq.c_str()] = deduced_from;
  }
  for (auto lit: overflowing_constraints){
    // if (overflowing_added > 0) break;
    auto p = var(lit);
    bool is_pos = lit.isPositive();
    Term poly = engine->arithmeticSolver->termOfPropositionalVariable(p);
    FF_ASSERT(LIA, dbla->isEq(poly));
    FF_ASSERT(LIA, dbla->arity(poly) == 2);
    //FF_ASSERT(LIA, dbla->term2string(dbla->ithChild(poly,1)) == dbla->term2string(dbla->addNum(0)));
    expr poly_exp_0 = term2z3expression(dbla,dbla->ithChild(poly,0),c);
    expr poly_exp_1 = term2z3expression(dbla,dbla->ithChild(poly,1),c);
    expr poly_exp = poly_exp_0;
    if (poly_exp_1 != c.int_val("0")) {
      poly_exp = poly_exp - poly_exp_1;
    } 
    string k_var_name = "_mk_"+ std::to_string(poly.ptr()->code());
    expr k_var = c.int_const(k_var_name.c_str());
    //expr k_bound = k_var >= c.int_val("0");
    expr k_expr =  k_var * c.int_val(prime.c_str());
    if (is_pos) {
      // std::cout << "Positive overflowing: " << dbla->term2string(poly) << std::endl;
      expr polyLeq = poly_exp <= k_expr;
      expr polyGeq = poly_exp >= k_expr;
      //expr polyEq = poly_exp == k_expr;
      // std::string propeq = "eq" + std::to_string(ecount++);
      std::string propeq = "eqk" + std::to_string(poly.ptr()->code());
      expr pe = polyLeq && polyGeq;
      //pe = pe.simplify();
      expr polyLeq1 = poly_exp_0 <= poly_exp_1;
      expr polyGeq1 = poly_exp_0 >= poly_exp_1;
      //expr polyEq1 = poly_exp_0 == poly_exp_1;
      expr pe1 = polyLeq1 && polyGeq1;
      //if (incremental) {
        // std::cout << "Checking " << pe <<  " with " << pe.id() << std::endl;
      if (sadded.find(pe.id()) == sadded.end() && sadded.find(pe1.id()) == sadded.end()) {
        // std::cout << "Positive overflowing added " << pe <<  " with " << pe.id() << std::endl;
        // std::cout << "Positive overflowing added " << " with " << pe.id() << std::endl;
          s.add(pe,propeq.c_str());
          sadded.insert(pe.id());
      //if (sadded.find(polyEq.id()) == sadded.end() && sadded.find(polyEq1.id()) == sadded.end()) {
         //std::cout << "Positive overflowing added " << polyEq <<  " with " << polyEq.id() << std::endl;
         //std::cout << "Positive overflowing added " << " with " << polyEq.id() << std::endl;
         // s.add(polyEq,propeq.c_str());
         // sadded.insert(polyEq.id());
          //s.add(k_bound);
          overflowing_added++;
          //cout << "counter " << overflowing_added << endl;
        }
      if (sadded.find(pe1.id()) == sadded.end()){
        Z3FFLiteralRelation[propeq.c_str()] = {p};
      }
      // cout << propeq.c_str() << ": ";
      // for (Var v:Z3FFLiteralRelation[propeq.c_str()]) {
      //   cout << v << ", ";
      // }
      // cout <<endl;
    } else {
      // std::cout << "Negative overflowing: " << dbla->term2string(poly) << std::endl;
      expr polyLt = poly_exp < k_expr;
      expr polyGt = poly_exp > k_expr;
      //expr polyNe = poly_exp != k_expr;
      // std::string propneq = "neq" + std::to_string(ncount++);
      std::string propneq = "neqk" + std::to_string(poly.ptr()->code());
      expr pn = polyLt || polyGt;
      //pn = pn.simplify();
      expr polyLt1 = poly_exp_0 < poly_exp_1;
      expr polyGt1 = poly_exp_0 > poly_exp_1;
      //expr polyNe1 = poly_exp_0 != poly_exp_1;
      expr pn1 = polyLt1 || polyGt1;
      // if (incremental) {
        // std::cout << "Checking " << pn <<  " with " << pn.id() << std::endl;
      if (sadded.find(pn.id()) == sadded.end() && sadded.find(pn1.id()) == sadded.end()) {
        //std::cout << "Negative overflowing added " << pn <<  " with " << pn.id() << std::endl;
        s.add(pn, propneq.c_str());
        sadded.insert(pn.id());
        //if (sadded.find(polyNe.id()) == sadded.end() && sadded.find(polyNe1.id()) == sadded.end()) {
        //std::cout << "Negative overflowing added " << pn <<  " with " << pn.id() << std::endl;
        //s.add(polyNe, propneq.c_str());
        // sadded.insert(polyNe.id());
         //s.add(k_bound);
        overflowing_added++;
        //cout << "counter " << overflowing_added << endl;
      }
      if (sadded.find(pn1.id()) == sadded.end()) {
        Z3FFLiteralRelation[propneq.c_str()] = {};
        Z3FFnegativeLiterals[propneq.c_str()] = lit;
      }
      // cout << propneq.c_str() << ": ";
      // for (Var v:deduced_from) {
      //   cout << v << ", ";
      // }
      // cout << Z3FFnegativeLiterals[propneq.c_str()] <<endl;
    }
    //std::cout << "end bounded lits" << std::endl;
    }
  std::cout << "LA checker ready " << s.assertions().size() << "; overflowing "<< overflowing_added << std::endl;
  //std::cout << s.to_smt2() << std::endl;
 // std::cout << s.assertions() << std::endl;
  
}

/* Precomputed, no needed
   void Solver::preprocess_info_constraints(
   const vector<Lit> & polynomials
   ){

   for (Lit l: polynomials){

   auto num = var(l);
   if(num == 0){
   continue;
   }
   // not only for positives, also study the negatives
   // if (l.isPositive()){

   auto pol = this->getPolynomial(num);

   map_to_unbounded_signals[num] = get_signals(pol);
   map_to_single_signals[num] = get_single_signals(pol);
   //}
   }

   cout << "Finished preprocess" <<endl;
   }
*/

void Solver::compute_bounds_signals(
				    const vector<Lit> & polynomials, bool is_leaf, bool la_over
				    ){

  vector<int> to_study;
  mpz_class p = mpz_class(prime);
  std::map<Var, bool> is_positive_pol;

  bool first_found = false;

  // Aux map to study which pols have just 0 or 1 unbounded signals
  std::map<uint, set<int>> map_to_unbounded_signals;

  // First round getting first set of bounds (binaries, constant, more rules to add)
  for (Lit l: polynomials){
    auto num = var(l);
    if(num == 0){
      continue;
    }

    //cout << to_string(l) << endl;
    // the bounds can only be deduced from positive literals
    if(l.isPositive()){

      if (polynomial_to_signals[num].size() <= 1){
        auto pol = this->getPolynomial(num);
        bool updated = detect_bounds_initial(pol, bounds, num, rooter);
        int signal = *polynomial_to_signals[num].begin();
        if (updated){
          if (!first_found){
            map_to_unbounded_signals = polynomial_to_signals;
            first_found = true;
          }
          to_study.push_back(signal);
          vector<Var> index_pols = signal_to_polynomials[signal];
          for (Var v: index_pols){
            if (map_to_unbounded_signals.count(v) > 0){
              map_to_unbounded_signals[v].erase(signal);
            }
          }

        }
      }
    }
    is_positive_pol[num] = l.isPositive();

  }


#if FF_PRINT

  cout << "Bounds after first deductions: " << endl;

  for (auto[signal, info]: bounds){
    cout << "Signal " << get_var_name(Context::Variable(signal)) << " is bounded between " <<  info.min << "-" << info.max << endl;
    cout << "-- Min deduced from: "<<endl;
    for (Var v: info.min_deduced_from){
      cout<< "-- " << this->getPolynomial(v)<<endl;
    }
    cout << "-- Max deduced from: "<<endl;
    for (Var v: info.max_deduced_from){
      cout<< "-- " << this->getPolynomial(v)<<endl;
    }
  }
#endif

  if (!first_found && !is_leaf){
    return;
  }

  int index = 0;
  vector<int> new_bounds;
  set<Var> studied_non_overflowing;

  while(index < int(to_study.size())){
    int bounded_signal = to_study[index];
    vector<Var> index_pols = signal_to_polynomials[bounded_signal];
    for(Var i: index_pols){
      bool added = false;
      auto pol = this->getPolynomial(i);
      // cout << "Try polynomial: " << pol << endl;
      // if it is in the ones that we are studying (should always be true?)
      if (is_positive_pol.count(i) > 0 && map_to_unbounded_signals.count(i) == 1){
        auto unbounded_signals_i = map_to_unbounded_signals[i];
        // for both positive and negative literals
        if(unbounded_signals_i.size() == 0 && studied_non_overflowing.count(i) == 0){
          // Add the constraint to the not overflowing if possible

          auto pol = this->getPolynomial(i);
          auto [max, conds_max] = get_max_value_polynomial(pol, bounds);
          auto [min, conds_min] = get_min_value_polynomial(pol, bounds);

          if (min > -p && max < p){
            // cout << "non-overflowing treated" << endl;
            added = true;
            set<Var> conditions = conds_min;
            conditions.merge(conds_max);
            studied_non_overflowing.insert(i);
            // if linear, add the literal and the conditions to the info of not overflowing
            if (is_linear(pol)) {
              not_overflowing_constraints.push_back({
                  Lit(i, is_positive_pol[i]),
		  conditions
		});
            }
          }
        } else if (unbounded_signals_i.size() == 1){
          // Check if it defines new bounds
          // only for positive literals

          if(is_positive_pol[i]){
            int signal = *unbounded_signals_i.begin();
            if (polynomial_to_single_signals[i].count(signal) == 1){
              // it is a single signal, we should study it
              auto pol = this->getPolynomial(i);
              bool updated = compute_bounds_signal(pol, bounds, signal, i);
              if (updated){
                to_study.push_back(signal);
                vector<Var> index_pols = signal_to_polynomials[signal];
                for (Var v: index_pols){
                  if (map_to_unbounded_signals.count(v) > 0){
                    map_to_unbounded_signals[v].erase(signal);
                  }
                }
                new_bounds.push_back(signal);
              }
            }
          }
        }
      }
    }
    index++;
  } 
  if (la_over) {
    for (Lit l: polynomials){
      auto num = var(l);
      if(num == 0){
        continue;
      }
      auto pol = this->getPolynomial(num);
      if (studied_non_overflowing.count(num) == 0 && is_linear(pol)){
        overflowing_constraints.push_back(l);
        
      }
    }
  }

  bool added_or = true;
  if(added_or){
    for (Lit l: polynomials){
      auto num = var(l);
      if(num == 0){
        continue;
      }
      auto pol = this->getPolynomial(num);

      if(l.isPositive() && pol.known_roots){ 
        auto unbounded_signals_i = map_to_unbounded_signals[num];
        // if not all signals are bounded or if it only has a root (linear already included) no need to analyse
        if(unbounded_signals_i.size() == 0 && pol.roots.size() > 1){
          
          vector<Polynomial<Zp>> pols_or;
          for (auto [signal, root]: pol.roots){
              Monomial x = Monomial(signal);
              Monomial one = Monomial();

              // Polynomial x == value
              Polynomial<Zp> x_is_value =  Polynomial<Zp>(1, x);
              if (root != 0){
                x_is_value = x_is_value + Polynomial<Zp>(-root, one);;
              }
              pols_or.push_back(x_is_value);
          }

          // TODO: not include if already added in the bounds?
          not_overflowing_disjunctions.push_back({pols_or, num});
        }
      
      }


    }
  }
#if FF_PRINT


  cout << "Bounds in final deductions: " << endl;

  for (int signal: new_bounds){
    auto info = bounds[signal];

    cout << "Signal " << get_var_name(Context::Variable(signal)) << " is bounded between " <<  info.min << "-" << info.max << endl;
    cout << "-- Min deduced from: "<<endl;
    for (Var v: info.min_deduced_from){
      cout<< "-- " << this->getPolynomial(v)<<endl;
    }
    cout << "-- Max deduced from: "<<endl;
    for (Var v: info.max_deduced_from){
      cout<< "-- " << this->getPolynomial(v)<<endl;
    }
  }

  cout << "Constraints that do not propagate: " << endl;
  for (auto[lit, deduced_from]: not_overflowing_constraints){
    cout << "*Polynomial " << to_string(lit) << " does not overflow*"<< endl;

    cout << "-- Deduced from: "<<endl;
    for (Var v: deduced_from){
      cout<< "-- " << this->getPolynomial(v)<<endl;
    }
  }
  for (auto lit: overflowing_constraints){
    cout << "*Polynomial " << to_string(lit) << " overflows*"<< endl;
  }
#endif
  cout << "Disjunctions that do not overflow: " << endl;
  for (auto[disj, deduced_from]: not_overflowing_disjunctions){
    cout << "Disjuction between" << endl;
    for (auto v: disj){
      cout<< "***" << v <<endl;
    }

    cout << "-- Deduced from: " << this->getPolynomial(deduced_from) <<endl;
    
  }

}


void Solver::compute_bounds_signals_complete(
  const vector<Lit> & polynomials, bool is_leaf, bool la_over
){
  compute_bounds_signals(polynomials,is_leaf, la_over);

  if (bounds.size() == 0) return;

  // For each one of the polynomials, decompose in the bounded and unbounded part
  // If the bounded part is between 0, p/2 --> we should study it
  mpz_class p = mpz_class(prime);

  map<Polynomial<Zp>, vector<Var>> unbounded_part_to_lits;
  map<Var, Polynomial<Zp>> lit_to_bounded_part;

  for (Lit l: polynomials){
    Polynomial<Zp> bounded_part;
    Polynomial<Zp> unbounded_part;

    auto num = var(l);
    if(num == 0){
      continue;
    }

    // We are only interested in the positive literals that have a linear bounded part
    if(l.isPositive()){
        auto pol = this->getPolynomial(num);

        bool is_valid = true;
        //cout << "Considering polynomial " << pol << endl;
        for (auto [monomial, coef]: pol){
          set<int> signals = get_signals(monomial);
          bool is_linear = is_single_signal(monomial);
          bool all_signals_mon_unbounded = true;
          for (int s: signals){
            if (bounds.count(s) > 0){
              all_signals_mon_unbounded = false;
              break;
            }
          }
          if (all_signals_mon_unbounded){
            unbounded_part = unbounded_part + Polynomial(coef, monomial);
          } else if (is_linear){
            bounded_part = bounded_part + Polynomial(coef, monomial);
          } else{
            is_valid = false;
            break;
          }
        }

        

        // in case it is interesting to consider it
        if (!is_zero(bounded_part) && !is_zero(unbounded_part) && is_valid){

          //cout << "It can be studied!" << endl;
          //cout << "Bounded part: " << bounded_part << endl;
          //cout << "Unbounded part: " << unbounded_part << endl;


          // check the max and min value of th bounded part
          auto [max, conds_max] = get_max_value_polynomial(bounded_part, bounds);
          auto [min, conds_min] = get_min_value_polynomial(bounded_part, bounds);

          //cout << "Min and max of bounded part: " << min << " " << max << endl;


          if (min >= 0 && max < p - 1){
            set<Var> conditions = conds_min;
            conditions.merge(conds_max);

            if (unbounded_part_to_lits.count(unbounded_part) > 0){
              unbounded_part_to_lits[unbounded_part].push_back(num);
            } else{
              unbounded_part_to_lits[unbounded_part] = {num};         

            }

            lit_to_bounded_part[num] =  bounded_part;


          } else if(min > -p + 1 && max <= 0){
            set<Var> conditions = conds_min;
            conditions.merge(conds_max);

            bounded_part = Zp(-1) * bounded_part;
            unbounded_part = Zp(-1) * unbounded_part;

            if (unbounded_part_to_lits.count(unbounded_part) > 0){
              unbounded_part_to_lits[unbounded_part].push_back(num);
            } else{
              unbounded_part_to_lits[unbounded_part] = {num};
            }

            lit_to_bounded_part[num] = bounded_part;
          }
        }
      }
    
  }

  // Create the new constraints --> single unbounded with multiple bounded
  for (auto [unb, list_v]: unbounded_part_to_lits){

    if (list_v.size() > 1){
      Var first_pol = list_v[0];
      auto pol = lit_to_bounded_part[first_pol];

      for (int i = 1; i < list_v.size(); i++){
        Var next_pol = list_v[i];
        auto new_pol = lit_to_bounded_part[next_pol];

        Polynomial<Zp> aux = Zp(-1) * new_pol;
        Polynomial<Zp> deduced_pol = pol + aux;
        auto [max, conds_max] = get_max_value_polynomial(deduced_pol, bounds);
        auto [min, conds_min] = get_min_value_polynomial(deduced_pol, bounds);

        if (min >= 1 - p && max < p - 1){
          set<Var> new_conds = conds_max;
          new_conds.merge(conds_min);
          new_conds.insert(first_pol);
          new_conds.insert(next_pol);

          deduced_not_overflowing.push_back({deduced_pol, new_conds});
        }
      }
    }
  }
  #if FF_PRINT

  cout << "Constraints deduced that do not overflow: " << endl;

  for (auto [pol, deduced_from]: deduced_not_overflowing){
    cout << "*Polynomial " << pol << " does not overflow*"<< endl;

    cout << "-- Deduced from: "<<endl;
    for (Var v: deduced_from){
      cout<< "-- " << this->getPolynomial(v)<<endl;
    }
  } 
  #endif

}




/////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////









vector<Lit> negate_literals(const vector<Lit> & lits){
  vector<Lit> result;

  for (Lit l: lits){
    result.push_back(~l);
  }

  return result;
}

int Solver::process_new_clause(const vector<Lit>& clause) {

#if FF_PRINT
  cout << "Processing new clause with: " << endl;
  for (Lit lit : clause) {
    cout << "   " << to_string(lit) << endl;
  }
  cout << endl;
#endif

#if FF_DEBUG
  vector<Lit> cube;
  for (Lit lit: clause) cube.push_back(lit.negation());
  FF_ASSERT(SOLVER, inconsistent(cube));
#endif

  int undef_1st = -1;
  int undef_2nd = -1;
  for (int k = 0; k < int(clause.size()); ++k) {
    Lit lit = clause[k];
    if (plit2exp.count(lit)) return 2;
    if (engine->isUndefLiteral(lit)) {
      if (undef_1st == -1) undef_1st = k;
      else                 undef_2nd = k;
    }
    else if (engine->isTrueLiteral(lit)) return 2;
  }

  if (undef_2nd != -1) { // Has at least two undefined literals -> add as a new clause.

    FF_ASSERT(SOLVER, undef_1st != undef_2nd);
    engine->clauseDataBase()->clearNewClause();
    engine->clauseDataBase()->addLiteralToNewClause(clause[undef_1st]);
    engine->clauseDataBase()->addLiteralToNewClause(clause[undef_2nd]);

    for (int k = 0; k < int(clause.size()); ++k)
      if (k != undef_1st and k != undef_2nd)
	engine->clauseDataBase()->addLiteralToNewClause(clause[k]);

    engine->clauseDataBase()->addNewClause(0, false, 0);

    return 1;
  }
  else if (undef_1st != -1) { // Propagates an undefined literal
    Lit plit = clause[undef_1st];
    auto it = plit2exp.find(~plit);
    if (it != plit2exp.end()) {         // Conflict with a propagated literal.
      conf_exp.clear();
      for (int k = 0; k < int(clause.size()); ++k)
        if (k != undef_1st)
          conf_exp.push_back(~clause[k]);
      for (Lit lit : it->second) conf_exp.push_back(lit);
      return -conf_exp.size();
    }
    else if (plit2exp[plit].empty()) {
      auto& exp = plit2exp[plit];
      plit_stack.push_back(plit);
      for (int k = 0; k < int(clause.size()); ++k)
        if (k != undef_1st)
          exp.push_back(~clause[k]);
    }
    return 0;
  }
  else { // Conflict.

    conf_exp.clear();
    for (Lit lit : clause) conf_exp.push_back(~lit);
    return -conf_exp.size();
  }
}


struct OrResult{
  bool isValid;
  vector<int> signals;
};

OrResult performOrCheck(const Polynomial<Zp>& pol){
  //std::cout << "Checking if Polynomial is Or condition: " << pol << std::endl;

  OrResult myResult;
  auto [is_or, possible_signals] = is_or_constraint(pol);
  myResult.isValid = is_or;
  myResult.signals = possible_signals;
  if (is_or){
    FF_OUT(SOLVER, "Found OR constraint! Generated by polynomial " << pol << endl);
  }
  return myResult;
}


struct BinaryResult{
  bool isValid;
  int signal;
};

BinaryResult performBinaryCheck(const Polynomial<Zp>& pol) {
  BinaryResult myResult;
  auto [is_binary, signal] = is_binary_constraint(pol);
  myResult.isValid = is_binary;
  myResult.signal = signal;
  if (is_binary){
    FF_OUT(SOLVER, "Found BINARY constraint! Generated by polynomial " << pol << endl);
  }
  return myResult;
}


// To detect constraints of the form signal*pol_b +pol_c = 0                (pol_c may be 0)
// We can introduce the constraints  pol_c = 0 ==> signal = 0 or pol_b = 0
//                                   siga  = 0 ==> polc = 0
//                                   polb  = 0 ==> polc = 0
struct CommonFactorResult{
  bool isValid;
  Vec<int> signals_a;
  Vec<Polynomial<Zp>> pols_b;
  Vec<Polynomial<Zp>> pols_c;
};
CommonFactorResult performCommonFactorCheck(const Polynomial<Zp>& pol){
  CommonFactorResult myResult;
  //std::cout << "Checking polynomial "<< pol <<std::endl;
  auto [hasCommonFactor, possible_signals] = has_common_signal(pol);
  if (hasCommonFactor){

    for (int signal: possible_signals){
      auto [pol_b, pol_c] = partition(pol, signal);
      myResult.signals_a.push(signal);
      myResult.pols_b.push(pol_b);
      myResult.pols_c.push(pol_c);
    }
    myResult.isValid = true;
    FF_OUT(SOLVER, "Found Common Factor constraint! -> Generated by polynomial: "<< pol << endl);
  } else{
    myResult.isValid = false;
  }
  return myResult;
}

int
Solver::performDeductionsFromPolynomial(const Polynomial<Zp> & pol, const vector<Lit> &lits, bool& inferred){

  // In case we deduce a clause C, we need to add !lit_poly or C

  int numPropagated = 0;


  // in case the roots are known use them
  if (pol.known_roots 
//    && !engine->arithmeticSolver->options.apply_la
  ){

    vector<Lit> lit_new_clause = negate_literals(lits);
    // generate the clause !lits or one of the signals = value
    for (auto [signal, value]: pol.roots){
      Lit lit_x_value = generate_x_equals_value(signal, value);
      lit_new_clause.push_back(lit_x_value);
    }

    int res = process_new_clause(lit_new_clause);
    if      (res  < 0) return res;
    else if (res == 0) ++numPropagated;
    else if (res == 1) inferred = true;

  } else{
     // check if the polynomial forces a signal s to be binary
    BinaryResult binResult = performBinaryCheck(pol);
    if (binResult.isValid){

      vector<Lit> lit_new_clause = negate_literals(lits);

      // add the constraints indicating that the signal is either 0 or 1
      Lit lit_x_0 = generate_x_equals_value(binResult.signal, 0);
      Lit lit_x_1 = generate_x_equals_value(binResult.signal, 1);

      lit_new_clause.push_back(lit_x_0);
      lit_new_clause.push_back(lit_x_1);


      int res = process_new_clause(lit_new_clause);
      if      (res  < 0) return res;
      else if (res == 0) ++numPropagated;
      else if (res == 1) inferred = true;
    } else{
      // check if the polynomial expresses an Or condition
      OrResult orResult = performOrCheck(pol);
      if (orResult.isValid){

        vector<Lit> lit_new_clause = negate_literals(lits);

        // add the constraints indicating that one of the signals should be 0
        for (int s: orResult.signals){
          Lit lit_s_0 = generate_x_equals_value(s, 0);
          lit_new_clause.push_back(lit_s_0);
        }

        int res = process_new_clause(lit_new_clause);
        if      (res  < 0) return res;
        else if (res == 0) ++numPropagated;
        else if (res == 1) inferred = true;
      } else{
        // check if we can extract common factor

        CommonFactorResult cfResult = performCommonFactorCheck(pol);
        if (cfResult.isValid){

          vector<Lit> lit_new_clause = negate_literals(lits);


          // for each one of the possible factors that can be extraced
          for (int i = 0; i < cfResult.signals_a.size(); i++){
            if (is_zero(cfResult.pols_c[i])){

              Lit lit_siga_0 = generate_x_equals_value(cfResult.signals_a[i], 0);
              Lit lit_polb_0 = generate_literal_from_polynomial(cfResult.pols_b[i]).first;
              Lit lit_polc_0 = generate_literal_from_polynomial(cfResult.pols_c[i]).first;
              auto a_name = get_var_name(Context::Variable(cfResult.signals_a[i]));
              // Add siga = 0 +or polb = 0
              lit_new_clause.push_back(lit_siga_0);
              lit_new_clause.push_back(lit_polb_0);
        int res = process_new_clause(lit_new_clause);
        if      (res  < 0) return res;
        else if (res == 0) ++numPropagated;
        else if (res == 1) inferred = true;
              lit_new_clause.pop_back();
              lit_new_clause.pop_back();
            } else{ // -> only if the literals are already created? For A, B and C or only A and B?

              // For now -> if literal A or B already exists, add condition A = 0 -> C = 0 and similar for B

              // Case B:
              /*
          if (containsAbstractedEquality(cfResult.pols_b[i])){
                Lit lit_polb_0 = generate_literal_from_polynomial(cfResult.pols_b[i]).first;
                Lit lit_polc_0 = generate_literal_from_polynomial(cfResult.pols_c[i]).first;

                // Add constraint B = 0 --> C = 0
                lit_new_clause.push_back(lit_polc_0);
                lit_new_clause.push_back(~lit_polb_0);
          int res = process_new_clause(lit_new_clause);
          if      (res  < 0) return res;
          else if (res == 0) ++numPropagated;
          else if (res == 1) inferred = true;
                lit_new_clause.pop_back();
                lit_new_clause.pop_back();

          }


              */

        // TODO: removing this case

        // Add polc != 0 or siga = 0 or polb = 0
        /*
          int res;
          lit_new_clause.push_back(~lit_polc_0);
          lit_new_clause.push_back(lit_siga_0);
          lit_new_clause.push_back(lit_polb_0);
          res = process_new_clause(lit_new_clause);
          if      (res  < 0) return res;
          else if (res == 0) ++numPropagated;
          else if (res == 1) inferred = true;
          lit_new_clause.pop_back();
          lit_new_clause.pop_back();
          lit_new_clause.pop_back();

          // Add siga != 0 or polc = 0
          lit_new_clause.push_back(lit_polc_0);
          lit_new_clause.push_back(~lit_siga_0);
          res = process_new_clause(lit_new_clause);
          if      (res  < 0) return res;
          else if (res == 0) ++numPropagated;
          else if (res == 1) inferred = true;
          lit_new_clause.pop_back();

          // Add polb != 0 or polc = 0
          lit_new_clause.push_back(~lit_polb_0);
          res = process_new_clause(lit_new_clause);
          if      (res  < 0) return res;
          else if (res == 0) ++numPropagated;
          else if (res == 1) inferred = true;
          lit_new_clause.pop_back();
          lit_new_clause.pop_back();

        */
            }
          }
        }


          // no roots now
          Propagator prop(rooter, pol);

          // Compute the roots of the polynomial and add linear constraints if found
          vector< vector< pair<Polynomial<Zp>, bool> > > res = prop.result();
          // A vector of class pair<Polynomial<Zp>,bool>   means their disjunction.
          // A vector of vector<pair<Polynomial<Zp>,bool>> means their conjunction.
          for (const vector< pair<Polynomial<Zp>, bool> >& v : res) {
            // For each one of the elements of the conjunction add a new clause
            vector<Lit> lit_new_clause = negate_literals(lits);
            for (const auto& [q, e] : v) {
              // for each one of the elements of the disjunction add a new literal to the clause
              Lit lit_q = generate_literal_from_polynomial(q).first;
              lit_new_clause.push_back(e ? lit_q : ~lit_q);
            }
            // add the new clause
      int res = process_new_clause(lit_new_clause);
      if      (res  < 0) return res;
      else if (res == 0) ++numPropagated;
      else if (res == 1) inferred = true;
          }



      }
    }
  }
  return numPropagated;
}


Term Solver::generate_term_from_polynomial(const Polynomial<Zp> & pol){
  // Abstract the polynomials in terms
  TermsDB* db = engine->termsDataBase();
  vector<pair<vector<pair<int, int>>, Zp>> values = destruct_polynomial(pol);

  bool is_first = true;
  Term term_poly = db->addNum(0);


  for (auto[signals, coef]: values){
    Term to_add;

    if (signals.size() != 0){
      bool is_first_coef = true;
      Term mon;
      for (auto[signal, exp]: signals){
        string var_signal  = get_var_name(Context::Variable(signal));
        Term term_signal = db->addTerm(var_signal);
        Term result = term_signal;
        for (int i = 0; i < exp-1; i++){
          result = db->addTimes(term_signal, result);
        }
        if (is_first_coef){
          mon = result;
          is_first_coef = false;
        } else{
          mon =  db->addTimes(mon, result);
        }
      }
      Term term_coef = db->addNum(coef);
      to_add = db->addTimes(mon, term_coef);

    } else{
      to_add = db->addNum(coef);
    }

    if (is_first){
      term_poly = to_add;
      is_first = false;
    } else{
      term_poly = db->addPlus(term_poly, to_add);
    }
  }
  // Term that represents that the polynomial value is 0
  Term eq = db->addEq(term_poly, db->addNum(0));
  return eq;
}

pair<Lit, bool> Solver::generate_literal_from_polynomial(const Polynomial<Zp> & pol){
  // Abstract the polynomials in terms
  TermsDB* db = engine->termsDataBase();
  vector<pair<vector<pair<int, int>>, Zp>> values = destruct_polynomial(pol);

  bool is_single_value = true;
  bool found_signal = false;
  bool is_first = true;
  Term term_poly = db->addNum(0);

  for (auto[signals, coef]: values){
    Term to_add;
    if (signals.size() != 0){
      bool is_first_coef = true;
      Term mon;
      for (auto[signal, exp]: signals){
        string var_signal  = get_var_name(Context::Variable(signal));
        Term term_signal = db->addTerm(var_signal);
        Term result = term_signal;
        for (int i = 0; i < exp-1; i++){
          result = db->addTimes(term_signal, result);
        }
        if (is_first_coef){
          mon = result;
          is_first_coef = false;
        } else{
          mon =  db->addTimes(mon, result);
        }
      }
      Term term_coef = db->addNum(coef);
      to_add = db->addTimes(mon, term_coef);

      if (found_signal){
        is_single_value = false;
      }
      found_signal = true;
    } else{
      to_add = db->addNum(coef);
    }

    if (is_first){
      term_poly = to_add;
      is_first = false;
    } else{
      term_poly = db->addPlus(term_poly, to_add);
    }
  }

  // Term that represents that the polynomial value is 0
  Term eq = db->addEq(term_poly, db->addNum(0));

  // Generate the literal and check if new
  pair<Lit, bool> result = engine->arithmeticSolver->abstractTheoryAtom(eq);
  // In case the atom is new we notify it to the linear solver
  if (result.second){
    int pvar = engine->newSplitVariable(SATSolver::FF_SOLVER);
    FF_ASSERT(SOLVER, Lit(pvar, true) == result.first);

    if (is_single_value){
      //std::cout << "Normalizing polynomial " << pol <<std::endl;
      Polynomial<Zp> simp_pol = normalize_single(pol);
      FF_ASSERT(SOLVER, simp_pol.is_normalized());
      //std::cout << "    " << simp_pol <<std::endl;
      lin_solver.defineNewEquality(pvar, simp_pol);
    } else{
      pol.normalize();
      FF_ASSERT(SOLVER, pol.is_normalized());
      lin_solver.defineNewEquality(pvar, pol);
    }

    // update the map signals to pols
    set<int> signals = get_signals(pol);
    for (int s: signals){
      signal_to_polynomials[s].push_back(pvar);
    }

    polynomial_to_signals[pvar] = signals;
    polynomial_to_single_signals[pvar] = get_single_signals(pol);

  }

  return result;
}

Lit Solver::generate_x_equals_value(int signal, Zp value){
  Monomial x = Monomial(signal);
  Monomial one = Monomial();

  // Polynomial x == value
  Polynomial<Zp> x_is_value;
  if (value == 0){
    x_is_value = Polynomial<Zp>(1, x);
  } else{
    Polynomial<Zp> aux_0 = Polynomial<Zp>(1, x);
    Polynomial<Zp> aux_1 = Polynomial<Zp>(-value, one);
    x_is_value = aux_0 + aux_1;
  }

  // Abstract the polynomials in terms
  string var_x  = get_var_name(Context::Variable(signal));
  TermsDB* db = engine->termsDataBase();
  Term term_x = db->addTerm(var_x);
  Term term_value = db->addNum(value);
  Term eq = db->addEq(term_x, term_value);

  // Generate the literal and check if new
  pair<Lit, bool> result = engine->arithmeticSolver->abstractTheoryAtom(eq);

  // In case the atom is new we notify it to the linear solver and add the info
  // to the map from signals to pols
  if (result.second){
    int pvar = engine->newSplitVariable(SATSolver::FF_SOLVER);
    FF_ASSERT(SOLVER, Lit(pvar, true) == result.first);
    FF_ASSERT(SOLVER, x_is_value.is_normalized());
    lin_solver.defineNewEquality(pvar, x_is_value);

    // update the map signals to pols
    signal_to_polynomials[signal].push_back(pvar);
    polynomial_to_signals[pvar] = {signal};
    polynomial_to_single_signals[pvar] = {signal};
  }

  return result.first;
}


struct EqualitiesResult{
  bool isValid;
  int signal_eliminated;
  int signal_remain;
};

EqualitiesResult get_equalities_variables(const Polynomial<Zp>& pol){
  std::ostringstream polynomialStream;

  //std::cout << "Checking if Polynomial is constant: " << pol << std::endl;
  EqualitiesResult result;
  result.isValid = false;

  // Case x = y
  if(pol.size() == 2){
    bool found_x = false;
    int x;
    Zp coef_x;

    for (const auto& [mon, coef] : pol) {
      if (coef != 0 && mon.size() == 1){ // possible x
        auto [u, e] = *mon.begin();
        if (e == 1){
          if (!found_x){
            found_x = true;
            coef_x = coef;
            x = u;
          } else{
            // check that we have coef * x + (-coef) * y
            if (coef_x == - coef){
              // in this case we have x - y == 0 --> OK

              result.isValid = true;
              if (x < u){
                result.signal_eliminated = u;
                result.signal_remain = x;
              } else{
                result.signal_eliminated = x;
                result.signal_remain = u;
              }
              return result;
            } else{
              return result;
            }
          }
        } else{
          return result;
        }
      } else{
        return result;
      }
    }
  }
  return result;

}


// Performs linear deduction of the assignment without propagating constants
// SIMPLE CHECK
int Solver::linear_clause_inference_simple(int level, bool& inferred) {

  // return 0;

  inferred = false;
  int numPropagated = 0;

  // Apply the deduction rules to the polynomials that have not been studied
  for(auto it_lit = this->getAssignment().begin(); it_lit != this->getAssignment().end(); ++it_lit) {

    auto num = var(*it_lit);
    if(num == 0){
      continue;
    }

    if (this->studied_polynomials.count({litAsUint(*it_lit)}) > 0){
      // We have already studied the polynomial, no need to study it again
      continue;
    }

    if(it_lit->isPositive()){
      // We study the polynomial and try to deduce linear constraint from it
      this->studied_polynomials.insert({litAsUint(*it_lit)});
      auto pol = this->getPolynomial(num);
      // no need to study the polynomial if it is already linear
      if (is_linear(pol)){
        continue;
      }
      int res = performDeductionsFromPolynomial(pol, {*it_lit}, inferred);
      if (res  < 0) return res;
      numPropagated += res;
    }
  }

  return numPropagated;

}


struct PolynomialInfo{
  Polynomial<Zp> pol;
  bool is_linear; // we use it to only add it in the first round that goes from linear to non linear
  vector<Lit> deduced_from;
};



// Performs linear deduction of the assignment propagating constants
// COMPLETE CHECK
int Solver::linear_clause_inference_complete(int level, bool& inferred) {

  // return 0;

  inferred = false;
  int numPropagated = 0;

  // First, find the signals that are assigned to constants and the propagate this info
  // After, study if new linear constraints can be deduced

  int num_constants = 0;
  int num_equalities = 0;


  // For signal-signal equalities propagation
  std::map<int, pair<vector<Lit>, int>> equalities;

  // For signal-constant equalities propagation
  std::map<int, pair<vector<Lit>, Zp>> constants;

  // signals that we need to study yet
  vector<int> to_study;

  // The new polynomials that we deduce after the propagation
  std::map<int, PolynomialInfo> pols_after_propagation;

  // Polynomials that we need to insert (the first time each one of them becomes linear)
  vector<PolynomialInfo> to_insert;

  //std::cout << "Starting constant propagation" <<std::endl;


  // First, we perform equalities propagation

  int pol_index = 0;
  int index = 0;

  for(auto it_lit = this->getAssignment().begin(); it_lit != this->getAssignment().end(); ++it_lit) {

    auto num = var(*it_lit);
    if(num == 0){
      continue;
    }

    auto pol = this->getPolynomial(num);

    if(it_lit->isPositive()){
      EqualitiesResult result = get_equalities_variables(pol);
      if (result.isValid){
	vector<Lit> conditions;
	conditions.push_back(*it_lit);
	equalities[result.signal_eliminated] = {conditions, result.signal_remain};
	to_study.push_back(result.signal_eliminated);
	num_equalities ++;
	//cout << "Variable " <<  get_var_name(Context::Variable(result.signal_eliminated)) << " has value -> " << get_var_name(Context::Variable(result.signal_remain)) <<std::endl;
      }
    }

    Polynomial<Zp> new_pol = pol;
    pols_after_propagation[num].pol = new_pol;
    pols_after_propagation[num].deduced_from = {*it_lit};
    pols_after_propagation[num].is_linear = is_linear(new_pol);
    pol_index++;
  }

  //std::cout<< "Found " << num_constants << " constant variables -> Start propagation" << std::endl;

  // Propagate all the constants, repeat the process until no more variables are infered



  while(index < int(to_study.size())){
    int eq_signal = to_study[index];
    auto [conditions, value] = equalities[eq_signal];
    //cout << "Propagating cte " << get_var_name(Context::Variable(eq_signal)) << " with value " <<  get_var_name(Context::Variable(value)) << std::endl;
    vector<uint> index_pols = signal_to_polynomials[eq_signal];

    for(uint i: index_pols){
      if (pols_after_propagation.count(i) > 0){
        auto previous_pol_info = pols_after_propagation[i];
        //cout << "Polynomial before assignment " << previous_pol_info.pol <<endl;

        Polynomial<Zp> new_pol = perform_assignment_to_signal(previous_pol_info.pol, eq_signal, value);
	FF_ASSERT(SOLVER, new_pol.ok());
        //cout << "Polynomial after assignment " << new_pol <<endl;
        // check conflicts:
        // Positive and 1 == 0
        bool is_conflict_positive = previous_pol_info.deduced_from.front().isPositive() && is_nonzero_constant(new_pol);
        // Negative and 0 == 0
        bool is_conflict_negative = previous_pol_info.deduced_from.front().isNegative() && is_zero(new_pol);

        bool new_is_linear = is_linear(new_pol);

        if (is_conflict_positive || is_conflict_negative){ // return the conflict
          conf_exp.clear();
          for (Lit info: previous_pol_info.deduced_from){
            conf_exp.push_back(info);
          }
          for (Lit info: conditions){
            conf_exp.push_back(info);
          }
          FF_OUT(SOLVER, "Found conflict after equalities propagation" << endl);
          return -conf_exp.size();

        } else if (!is_zero(new_pol)){ // standard case, no conflicts

	  new_pol.normalize();
	  //std::cout << "Polynomial after propagation " << new_pol << std::endl;
	  for (Lit info: conditions){
	    previous_pol_info.deduced_from.push_back(info);
	  }

	  pols_after_propagation[i].pol = new_pol;
          pols_after_propagation[i].is_linear = new_is_linear;
          pols_after_propagation[i].deduced_from = previous_pol_info.deduced_from;

	  // Check if it generates a new constant (only for positives)
          if (previous_pol_info.deduced_from.front().isPositive()){
            EqualitiesResult result = get_equalities_variables(new_pol);
	    if (result.isValid && equalities.count(result.signal_eliminated) == 0){
	      equalities[result.signal_eliminated] = {previous_pol_info.deduced_from, result.signal_remain};
	      to_study.push_back(result.signal_eliminated);
	      num_equalities ++;
              //std::cout << "Variable " <<  get_var_name(Context::Variable(result.signal_eliminated)) << " has value -> " << get_var_name(Context::Variable(result.signal_remain)) <<std::endl;
	    }
          }

          // Check if it becomes linear for the first time (and if so add to to_insert)
          if (!previous_pol_info.is_linear && new_is_linear){
            to_insert.push_back(pols_after_propagation[i]);
          }

          // Check in case no linear if it generates new linears after applying rules
          if (!new_is_linear){
            // Check if we have already studied
            vector<uint> literals_applied;
            for (Lit l: pols_after_propagation[i].deduced_from){
              literals_applied.push_back(litAsUint(l));
            }
            if (this->studied_polynomials.count(literals_applied) > 0){
              // We have already studied the polynomial, no need to study it again
              continue;
            }
            this->studied_polynomials.insert(literals_applied);

            int res = performDeductionsFromPolynomial(pols_after_propagation[i].pol, pols_after_propagation[i].deduced_from, inferred);
            if (res  < 0) return res;
            numPropagated += res;
          }
        }
      }

    }
    index++;
  }


  for (auto pol_info: to_insert){
    // no need to study if already studied
    vector<uint> literals_applied;
    for (Lit l: pol_info.deduced_from){
      literals_applied.push_back(litAsUint(l));
    }

    if (this->studied_polynomials.count(literals_applied) > 0){
      // We have already studied the polynomial, no need to study it again
      continue;
    }
    this->studied_polynomials.insert(literals_applied);


    // Insert the new polynomial
    vector<Lit> lit_new_clause = negate_literals(pol_info.deduced_from);
    Lit lit_pol = generate_literal_from_polynomial(pol_info.pol).first;
    if (pol_info.deduced_from.front().isNegative()) lit_pol = ~lit_pol;
    lit_new_clause.push_back(lit_pol);
    // add the new clause
    int res = process_new_clause(lit_new_clause);
    if      (res  < 0) return res;
    else if (res == 0) ++numPropagated;
    else if (res == 1) inferred = true;
  }

  // Secondly, we perform constant propagation
  pol_index = 0;
  to_study.clear();
  to_insert.clear();

  for(auto it_lit = this->getAssignment().begin(); it_lit != this->getAssignment().end(); ++it_lit) {

    auto num = var(*it_lit);
    if(num == 0){
      continue;
    }

    auto pol = this->getPolynomial(num);

    if(it_lit->isPositive()){
      ConstantsResult result = get_constant_variables(pol);
      if (result.isValid){
	vector<Lit> conditions;
	conditions.push_back(*it_lit);
	constants[result.signal] = {conditions, result.value};
	to_study.push_back(result.signal);
	num_constants ++;
	//std::cout << "Variable " <<  get_var_name(Context::Variable(result.signal)) << " has constant value -> " << result.value <<std::endl;
      }

    }

    Polynomial<Zp> new_pol = pol;
    pols_after_propagation[num].pol = new_pol;
    pols_after_propagation[num].deduced_from = {*it_lit};
    pols_after_propagation[num].is_linear = is_linear(new_pol);
    pol_index++;
  }

  //std::cout<< "Found " << num_constants << " constant variables -> Start propagation" << std::endl;

  // Propagate all the constants, repeat the process until no more variables are infered

  index = 0;

  while(index < int(to_study.size())){
    int cte_signal = to_study[index];
    auto [conditions, value] = constants[cte_signal];
    //cout << "Propagating cte " << get_var_name(Context::Variable(cte_signal)) << " with value " << value << std::endl;
    vector<uint> index_pols = signal_to_polynomials[cte_signal];

    for(uint i: index_pols){
      if (pols_after_propagation.count(i) > 0){

        auto pol_info = pols_after_propagation[i];
        //cout << "Polynomial before assignment " << pol <<endl;
        Polynomial<Zp> new_pol = perform_assignment(pol_info.pol, cte_signal, value);
        //cout << "Polynomial after assignment " << new_pol <<endl;

        // check conflicts:
        // Positive and 1 == 0
        bool is_conflict_positive = pol_info.deduced_from.front().isPositive() && is_nonzero_constant(new_pol);
        // Negative and 0 == 0
        bool is_conflict_negative = pol_info.deduced_from.front().isNegative() && is_zero(new_pol);

        bool new_is_linear = is_linear(new_pol);

        if (is_conflict_positive || is_conflict_negative){ // return the conflict

          conf_exp.clear();
          for (Lit info: pol_info.deduced_from){
            conf_exp.push_back(info);
          }
          for (Lit info: conditions){
            conf_exp.push_back(info);
          }
          FF_OUT(SOLVER, "Found conflict after constants propagation" << endl);
          return -conf_exp.size();

        } else if (!is_zero(new_pol)){ // standard case
	  new_pol.normalize();
	  //std::cout << "Polynomial after propagation " << new_pol << std::endl;
	  for (Lit info: conditions){
	    pol_info.deduced_from.push_back(info);
	  }

          pols_after_propagation[i].pol = new_pol;
          pols_after_propagation[i].is_linear = new_is_linear;
          pols_after_propagation[i].deduced_from = pol_info.deduced_from;

	  // Check if it generates a new constant (only for positives)
          if (pol_info.deduced_from.front().isPositive()){
            ConstantsResult result = get_constant_variables(new_pol);
	    if (result.isValid && constants.count(result.signal) == 0){
	      constants[result.signal] = {pol_info.deduced_from, result.value};
	      to_study.push_back(result.signal);
	      num_constants ++;
	      //std::cout << "Variable " <<  get_var_name(Context::Variable(result.signal)) << " has value -> " << result.value <<std::endl;
	    }
          }

          // Check if it becomes linear for the first time (and if so add to to_insert)
          if (!pol_info.is_linear && new_is_linear){
            to_insert.push_back(pols_after_propagation[i]);
          }

          // Check in case no linear if it generates new linears after applying rules
          if (!new_is_linear){
            // Check if we have already studied
            vector<uint> literals_applied;
            for (Lit l: pols_after_propagation[i].deduced_from){
              literals_applied.push_back(litAsUint(l));
            }
            if (this->studied_polynomials.count(literals_applied) > 0){
              // We have already studied the polynomial, no need to study it again
              continue;
            }
            this->studied_polynomials.insert(literals_applied);

            int res = performDeductionsFromPolynomial(pols_after_propagation[i].pol, pols_after_propagation[i].deduced_from, inferred);
            if (res  < 0) return res;
            numPropagated += res;
          }
        }
      }

    }
    index++;
  }

  //std::cout << "Finished constant propagation" <<std::endl;

  for (auto pol_info: to_insert){
    // no need to study if already studied
    vector<uint> literals_applied;
    for (Lit l: pol_info.deduced_from){
      literals_applied.push_back(litAsUint(l));
    }


    if (this->studied_polynomials.count(literals_applied) > 0){
      // We have already studied the polynomial, no need to study it again
      continue;
    }
    this->studied_polynomials.insert(literals_applied);


    // Insert the new polynomial
    vector<Lit> lit_new_clause = negate_literals( pol_info.deduced_from);
    Lit lit_pol = generate_literal_from_polynomial(pol_info.pol).first;
    if (pol_info.deduced_from.front().isNegative()) lit_pol = ~lit_pol;
    lit_new_clause.push_back(lit_pol);
    // add the new clause
    int res = process_new_clause(lit_new_clause);
    if      (res  < 0) return res;
    else if (res == 0) ++numPropagated;
    else if (res == 1) inferred = true;
  }


  return numPropagated;
}


int Solver::check_consistency(int level) {

  static int check_consistency_counter = 0;
  ++check_consistency_counter;
  
  constexpr int LEAF = 0;

  constexpr int      SAT = 0;
  constexpr int  UNKNOWN = 1;
  constexpr int UNSOLVED = 2;

  if (FIRE(light_check_determinism)) {
    if (engine->stats.decisionLevel == 0) {
      int res = check_consistency_light();
      if (res < 0) return res; // If a conflict has been found, done.
      if (res > 0) {
        if (level == LEAF)
          return UNSOLVED;// SAT solver will loop again and call propagate()
        else
          return SAT;     // SAT solver will now call theoryPropagate
      }
    }
  }

  if (FIRE(linear_solver)) {
    int res = lin_solver.checkConsistency(level);
    if (res < 0) return res;
    if (res == SAT and level == LEAF)
      return SAT; // At leaves, SAT results of linear solver are sound.
  }
  
  if (FIRE(apply_la)) {
    if (level == LEAF) std::cout << "CALLING LA IN A LEAF" << std::endl;
    int res = check_consistency_la(engine->arithmeticSolver->options.apply_la_incremental, FIRE(complete_non_overflowing_deductions),level == LEAF,FIRE(la_with_overflowing_constraints));
    //if (res <= 0){
  if (res < 0){
      return res;
    }
  }

  if (FIRE(linear_solver)) {
    int res = lin_solver.theoryPropagate(level);
    if (res < 0) {
      FF_OUT(SOLVER, "Conflict detected by theory propagate" << endl);
      return res;
    }
    if (res > 0) {
      if (level == LEAF) return UNSOLVED;
      else               return SAT;
    }
  }

  bool inferred = false;

  if (FIRE(simple_deductions)) {    
    FF_OUT(SOLVER, "Calling to simple inference" << endl);
    int res = linear_clause_inference_simple(level, inferred);
    if (res < 0)  return res;
    if (res > 0) {
      if (level == LEAF) return UNSOLVED;
      else               return SAT;
    }
    if (inferred)        return UNSOLVED;
  }

  if (FIRE(complete_deductions)) {
    FF_OUT(SOLVER, "Calling to complete inference" << endl);

    int res = linear_clause_inference_complete(level, inferred);
    if (res < 0)  return res;
    if (res > 0) {
      if (level == LEAF) return UNSOLVED;
      else               return SAT;
    }
    if (inferred)        return UNSOLVED;
  }

  // Only call nonlinear solver at leaves.
  if (level == LEAF) {
    int res = check_consistency_with_non_linear_solver(LEAF);
    if (res == 0) {
      if (assignment_is_satisfied(solution)) {
        cout << "NRA correct solution" << endl;
        return res;
      } else {
        cout << "NRA incorrect solution" << endl;
        return UNKNOWN;
      }
    }
    return res;
  }
  else               return UNKNOWN;
}


Solver::Solver(::SATSolver* s) :
  cons_db          ( ),
  engine           (s),
  //  la_solver        (s),
  lin_solver       (*this),
  nonlin_solver    (*this, engine->arithmeticSolver->options.apply_nra, engine->arithmeticSolver->options.using_cocoa),
  time_non_linear  (0),
  next             (0),
  //LIACalls (0),
  timeout (900),
  z3c ( ),
  // simp (z3c,Z3_simplifier()),
  z3solver(z3c,"QF_LIA")
  // z3solver(z3c,simp) //,
  //z3p(z3c)
{
  //z3solver.set("smt.core.minimize",true);// "sat.core.minimize"
  /*
  z3::param_descrs p = z3solver.get_param_descrs ();
  std::cout << "Parameters!!!" << std::endl;
  std::cout << p << std::endl;
  std::cout << "Help!!!" << std::endl;
  std::cout << Z3_solver_get_help(z3c,z3solver)<< std::endl;
  z3solver.set("logic",z3::symbol(z3c,z3c.str_symbol("lia")));
  //z3solver.set("ignore_solver1",true);
  z3solver.set("delay_units",true);
  uint arith = 2;//6
  z3solver.set("arith.solver", arith);
  uint st = 2;
  z3solver.set("restart_strategy", st);
  //z3solver.set("restart_factor",1.2);
  */
  //z3solver.set("arith.random_initial_value",true);
  //z3solver.set("",);
  //unsigned sz = p.size();
  //for (unsigned i = 0; i < sz; ++i) {
  //      symbol nm = p.name(i);
  //}
  //z3solver.set("sat.restart.max", 100);
  //uint timeout = 1000;
  //z3p.set("timeout", timeout);
  //z3solver.set(z3p);
  //z3solver.set("timeout", timeout);
  //la_solver.notifyStrategy(s);
}


void Solver::backtrack(int n) {

  FF_OUT(SOLVER, "backtrack(" << n << ")" << endl);

  if (n == 0) return; // Nothing to be done.

  if (engine->arithmeticSolver->options.apply_la && engine->arithmeticSolver->options.apply_la_incremental) {
    z3solver.pop(n);
  }

  Lit mark;

  // Restore the stack of propagated literals and their explanations.
  mark = Lit(1, true);
  int s = plit_stack.size();
  int p = n;
  while (p > 0) {
    FF_ASSERT(SOLVER, s > 0);
    Lit lit = plit_stack[s-1];
    while (lit != mark) {
      FF_OUT(SOLVER, "clear explanation of propagated literal " << to_string(lit) << endl);
      plit2exp.erase(lit);
      --s;
      FF_ASSERT(SOLVER, s > 0);
      lit = plit_stack[s-1];
    }
    --s;
    --p;
  }
  plit_stack.resize(s);
  if (next > s) next = s;

  // Restore the stack of asserted literals.
  mark = Lit();
  int h = assignment.size();
  int q = n;
  while (q > 0) {
    FF_ASSERT(SOLVER, h > 0);
    Lit lit = assignment[h-1];
    while (lit != mark) {
      FF_OUT(SOLVER, "unassign " << to_string(lit) << endl);
      --h;
      FF_ASSERT(SOLVER, h > 0);
      lit = assignment[h-1];
    }
    --h;
    --q;
  }
  lin_solver.   backtrack(n);
  nonlin_solver.backtrack(n);
  assignment.resize(h);
}


bool Solver::inconsistent(const vector<Lit>& conflict) {

  static int num_queries = 0;
  ++num_queries;
  // Create unique filenames to avoid interference across runs.

  uint64_t __ff_rand = std::time(nullptr);
  std::string random_suffix = "_" + std::to_string(__ff_rand);

  std::string mapleInputFilename  = std::string("./maple_input")  + random_suffix + ".txt";
  std::string mapleOutputFilename = std::string("./maple_output") + random_suffix + ".txt";
  std::string mapleFilterFilename = std::string("./maple_filter") + random_suffix + ".txt";

  ostringstream result;
  bool firstPoly = true;
  for (Lit lit : conflict) {

    if (lit == Lit(1,  true)) continue;
    if (lit == Lit(1, false)) return true;

    if (not firstPoly) result << ", "; // Sep between polynomials.
    firstPoly = false;
    set<string> variablesInPols;
    literal2maple_pol(result, *this, lit, variablesInPols);
  }

  stringstream list_of_polynomials;
  list_of_polynomials << "polys := [" << result.str() << "]:";

  stringstream groebner_basis;
  groebner_basis << "b := Basis(polys, tord" << num_queries <<", characteristic=" << prime << ", output=extended):";

  string final_query = "fprintf(f, \"%a\\n\", member(1, b[1])); for i to nops(b[2][1]) do if b[2][1][i] <> 0 then fprintf(f, \"%d\\n\", 1); else fprintf(f, \"%d\\n\", 0); end if; end do; fprintf(f, \"\\n\");";

  ofstream out(mapleInputFilename);
  FF_ASSERT(NONLINEAR, out.is_open());
  out << "\n with(Groebner):"      << "\n"
      << list_of_polynomials.str() << "\n"
      << groebner_basis.str()      << "\n"
      << "f := fopen(\"" << mapleOutputFilename << "\", 'WRITE', 'TEXT'):" << "\n"
      << final_query               << "\n"
      << "fclose(f):"              << "\n";
  out.close();
  system(string("maple -q < " + mapleInputFilename + " > /dev/null 2>&1").c_str());

  system(string("grep --invert-match \"kilobytes\" " + mapleOutputFilename + " > " + mapleFilterFilename + " 2> /dev/null").c_str());

  ifstream inFile(mapleFilterFilename);
  FF_ASSERT(NONLINEAR, inFile.is_open());

  string isTrivial;
  inFile >> isTrivial;
  inFile.close();

  return isTrivial == "true";
}


int Solver::check_consistency_light() {
  FF_OUT(SOLVER, "Performing light check" << endl);

  int num_vars = get_num_vars();
  vector<int > par(num_vars, -1);

  auto representative = [&](int x) -> int {
    auto representative_aux = [&](const auto &self, int x) -> int {
      if (par[x] == -1) return x;
      else return par[x] = self(self, par[x]);
    };
    return representative_aux(representative_aux, x);
  };

  auto merge = [&](int x, int y) {
    int rx = representative(x);
    int ry = representative(y);
    if (rx != ry)
      par[rx] = ry;
  };

  vector<Lit> pending;
  for (Lit lit : assignment)
    if (lit.isPositive())
      pending.push_back(lit);

  int w = 0;
  for (int r = 0; r < int(pending.size()); ++r) {
    Lit lit = pending[r];
    const auto& pol = getPolynomial(var(lit));

    if (pol.size() == 2) {
      auto it_1st = pol.begin();
      auto it_2nd = it_1st;
      ++it_2nd;
      if (is_single_signal(it_1st->first) and
          is_single_signal(it_2nd->first) and
          it_1st->second == -it_2nd->second) {        // a * x - a * y == 0
	int x = *(get_signals(it_1st->first).begin());
	int y = *(get_signals(it_2nd->first).begin());
	merge(x, y);
      }
      else {
	pending[w] = lit;
	++w;
      }
    }
    else {
      pending[w] = lit;
      ++w;
    }
  }
  pending.resize(w);

  bool changed = true;
  while (changed) {

    changed = false;

    map<Polynomial<Zp>, vector<int> > poly2vars;
    for (Lit lit : pending) {
      const auto& pol = getPolynomial(var(lit));
      int  x  = -1;
      auto xt = pol.mon2coeff.end();
      for (auto it = pol.mon2coeff.begin(); it != pol.mon2coeff.end(); ++it) {
        const auto& mon = it->first;
        if (is_single_signal(mon)) {
          x = *(get_signals(mon).begin());
          xt = it;
          bool ok = true;
          for (auto jt = pol.mon2coeff.begin(); jt != pol.mon2coeff.end(); ++jt) {
            if (jt == it) continue;
            if (contains_signal(jt->first, x)) {
              ok = false;
              break;
            }
          }
          if (ok) break;
          else {
            x = -1;
            xt = pol.mon2coeff.end();
          }
        }
      }
      if (x != -1) {
        Polynomial<Zp> p = pol;
        p = p + Polynomial<Zp>(-xt->second, xt->first);

        Polynomial<Zp> q;
        for (const auto& [p_mon, coeff] : p.mon2coeff) {
          Monomial q_mon;
          for (const auto& [p_var, exp] : p_mon.w) {
            int q_var = representative(p_var);
            q_mon = q_mon * Monomial(q_var, exp);
          }
          q = q + Polynomial<Zp>(coeff, q_mon);
        }
        poly2vars[q].push_back(x);
      }
    }

    for (const auto& [_, vars] : poly2vars) {
      int x = vars[0];
      for (int k = 1; k < int(vars.size()); ++k) {
        int y = vars[k];
        if (representative(x) != representative(y)) {
          merge(x, y);
          changed = true;
        }
      }
    }
  }

  // Assert the equalities that we have discovered.
  int numPropagated = 0;
  for (int s = 0; s < num_vars; s++) {
    int equiv = representative(s);
    if (s != equiv){
      Polynomial<Zp> aux_0 = Polynomial<Zp>(1, s);
      Polynomial<Zp> aux_1 = Polynomial<Zp>(-1, equiv);
      Polynomial<Zp> eq = aux_0 + aux_1;
      auto [new_lit, is_new] = generate_literal_from_polynomial(eq);
      vector<Lit> clause = {new_lit};
      for (Lit lit : assignment) clause.push_back(~lit);
      int res = process_new_clause(clause);
      FF_ASSERT(SOLVER, res != 1);
      if      (res  < 0) return res;
      else if (res == 0) ++numPropagated;
    }
  }

  return numPropagated;
}


int Solver::checkConsistency(int level) {

  FF_OUT(SOLVER, "checkConsistency with level " << level << "\n");

#if FF_PRINT
  string tab(3, ' ');
  cout << tab << "BEGIN assignment " << endl;
  for (Lit lit : assignment) {
    cout << tab;
    if (lit == Lit()) cout <<  "----"        << endl;
    else              cout << to_string(lit) << endl;
  }
  cout << tab << "END assignment" << endl;
  // cout << tab << "BEGIN model " << endl;
  // auto& v = (engine->model).modelStack;
  // for (int k = 0; k < v.size(); ++k) {
  //   Lit lit = v[k];
  //   if (not engine->isTheoryVar(var(lit))) continue;
  //   cout << tab;
  //   if (lit == Lit()) cout <<  "----"        << endl;
  //   else              cout << to_string(lit) << endl;
  // }
  // cout << tab << "END model" << endl;
#endif // FF_PRINT

#if FF_DEBUG
  for (Lit lit : assignment)
    FF_ASSERT(SOLVER, lit == Lit() or engine->isTrueLiteral(lit));
#endif // FF_DEBUG

  int res = check_consistency(level);
  // To avoid problems with repeated literals, if any.
  if (res < 0) {
    set<Lit> tmp;
    for (Lit lit : conf_exp) tmp.insert(lit);
    conf_exp = vector<Lit>(tmp.begin(), tmp.end());
    res = -conf_exp.size();
  }

  FF_OUT(SOLVER, "checkConsistency returns " << res << "\n");

#if FF_PRINT
  if (res < 0) { // Check the explanation of the conflict with Maple.
    cout << "Conflict:" << endl;
    for (int i = 1; i <= -res; ++i)
      cout << to_string( ithInconsist(i) ) << endl;
  }
#endif // FF_PRINT

#if FF_DEBUG
  if (res < 0) { // Check the explanation of the conflict with Maple.
    vector<Lit> conflict;
    for (int i = 1; i <= -res; ++i) {
      Lit lit = ithInconsist(i);
      FF_ASSERT(SOLVER, engine->isTrueLiteral(lit));
      conflict.push_back(lit);
    }
    FF_ASSERT(SOLVER, inconsistent(conflict));
  }
  else if (res == 0 and level == 0) { // Check the solution if at a leaf.
    FF_ASSERT(SOLVER, assignment_is_satisfied(solution));
  }
#endif // FF_DEBUG

  return res;
}


void Solver::initializeAfterParsing() {
  FF_OUT(SOLVER, endl << "Finite field solver initializing..." << endl << endl);

#if FF_PRINT

  for (const auto& [pvar, poly] : cons_db) {
    cout << "Propositional variable " << pvar << "\t<~~> " << poly << " == 0" << endl;
  }

#endif

  auto is_equivalence_or_assignment = [](const Polynomial<Zp>& poly) {
    if (poly.size() == 1) {
      auto it_1st = poly.begin();
      return is_single_signal(it_1st->first);
    }
    else if (poly.size() == 2) {
      auto it_1st = poly.begin();
      auto it_2nd = it_1st;
      ++it_2nd;
      if (is_single_signal(it_1st->first) and
          is_single_signal(it_2nd->first) and
          it_1st->second == -it_2nd->second) {
	return true;
      }
      else if (is_single_signal(it_1st->first) and is_one(it_2nd->first)) {
	return true;
      }
      else if (is_single_signal(it_2nd->first) and is_one(it_1st->first)) {
	return true;
      }
      else return false;
    }
    else return false;
  };
  
  bool all_equivalences_or_assignments = true;
  for (const auto& [pvar, poly] : cons_db) {
    if (not is_equivalence_or_assignment(poly)) {
      // cout << "guilty: " << poly << endl;
      all_equivalences_or_assignments = false;
      break;
    }
  }

  // cerr << "all_equivalences_or_assignments: " << all_equivalences_or_assignments << endl;

  if (all_equivalences_or_assignments) {
    // cerr << "override user options" << endl;
    // Overrride user options.
    engine->arithmeticSolver->options.light_check_determinism = 0;
    engine->arithmeticSolver->options.apply_la = 0;
    engine->arithmeticSolver->options.complete_non_overflowing_deductions = 0;
    engine->arithmeticSolver->options.simple_deductions = 0;
    engine->arithmeticSolver->options.complete_deductions = 0;
  }
  
  lin_solver   .initializeAfterParsing();
  nonlin_solver.initializeAfterParsing();
  //la_solver.initializeAfterParsing();

  // TODO: move to aux function for clarity
  // Initialize the map containing the relation from signals to polynomials in which they appear
  for (const auto& [pvar, poly] : cons_db) {
    set<int> signals = get_signals(poly);

    // To transform the lit into a var with the info
    //cout << "Polynomial " << pvar << ": " << poly << endl;
    for (int s: signals){
      if (signal_to_polynomials.count(s)){
	signal_to_polynomials[s].push_back(pvar);
      } else{
	signal_to_polynomials[s] = {pvar};
      }
    }
    polynomial_to_signals[pvar] = signals;
    polynomial_to_single_signals[pvar] = get_single_signals(poly);
  }

  for (const auto& [pvar, poly] : cons_db)
    if (is_linear(poly)) {
      engine->varActivity[pvar] = 100;
      engine->maxHeap.updateScore(pvar);
    }

  FF_OUT(SOLVER, endl << "... finite field solver initialized" << endl << endl);
}


void Solver::setBTPoint() {
  FF_OUT(SOLVER, "setBTPoint" << endl);
  assignment.push_back(Lit());        // Lit()       used as a mark for backtracking in assignment.
  plit_stack.push_back(Lit(1, true)); // Lit(1,true) used as a mark for backtracking in propagated lits.
  lin_solver.   setBTPoint();
  nonlin_solver.setBTPoint();
  if (engine->arithmeticSolver->options.apply_la && engine->arithmeticSolver->options.apply_la_incremental) {
    z3solver.push();
  }
}


bool Solver::assignment_is_satisfied(const map<string, Zp>& solution) {
  vector<Zp> var2val(cons_db.get_num_vars());
  for (const auto& [name, value] : solution)
    var2val[cons_db.identifier(name)] = value;

  for (Lit lit : assignment) {
    if (lit == Lit()) continue;
    const Polynomial<Zp>& p = cons_db.polynomial(var(lit));
    Zp eval= p.evaluate(var2val);
    if (isPositive(lit) != (eval == Zp(0))) {
      /* std::cout << "Fails: " << p << " == " << isPositive(lit) << std::endl;
      std::cout << "Solution: " << std::endl;
      for (auto const& nv: solution) {
        std::cout << nv.first << ": " << nv.second << std::endl;
        }*/
      return false;
    }
  }
  return true;
}

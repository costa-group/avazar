#ifndef FF_SOLVER_INLINES_HPP
#define FF_SOLVER_INLINES_HPP

#include "Constraint_database.inlines.hpp"
#include "Linear_solver.inlines.hpp"
#include "Nonlinear_solver.inlines.hpp"

#include "Solver.defs.hpp"


namespace FF {

inline void Solver::notifyTermsDataBase (::TermsDB* db) {
  //la_solver.notifyTermsDataBase(db);
}

inline Solver::~Solver() { }

inline int Solver::get_num_vars() const {
  return cons_db.get_num_vars();
}

inline bool Solver::is_var(string name) const {
    return cons_db.is_var(name);
}

inline Lit Solver::abstractLiteral(TermsDB &DB, Term t, int p) {
  return cons_db.abstract_equality(DB, t, p);
}

inline bool Solver::containsAbstractedEquality(const Polynomial<Zp> & eq) {
  return cons_db.contains_abstracted_equality(eq);
}

inline const Polynomial<Zp>& Solver::getPolynomial(int p) const {
  return cons_db.polynomial(p);
}

inline string Solver::to_string(Lit l) {
  ostringstream ost;
  if (l == Lit())              ost << "literal NULL";
  else if (l == Lit(1, true) ) ost << "literal TRUE";
  else if (l == Lit(1, false)) ost << "literal FALSE";
  else {
    ost << "literal " << l << ", constraint ";
    ost << cons_db.polynomial(var(l)) << (l.isPositive() ? " == 0" : " != 0");
  }
  return ost.str();
}


inline void Solver::setTrue(Lit l) {
  FF_OUT(SOLVER, "set True " << to_string(l) << endl);
  assignment.push_back(l);
  lin_solver.setTrue(l);
}


inline Lit Solver::ithInconsist(int i) {
  FF_ASSERT(SOLVER, i >= 1);
  FF_ASSERT(SOLVER, i <= int(conf_exp.size()));
  Lit l = conf_exp[i-1];
  FF_ASSERT(SOLVER, l != Lit());
  FF_OUT(SOLVER, "ithInconsist(" << i << ") returns " << to_string(l) << endl);
  return l;
}


inline int Solver::theoryPropagate(int level) {
  int res = plit_stack.size() - next;
  next = plit_stack.size();
  FF_OUT(SOLVER, "theoryPropagate returns " << res << endl);

  return res;
}


inline Lit Solver::ithConseq(int i) {
  int s = plit_stack.size();
  FF_ASSERT(SOLVER, i >= 1);
  FF_ASSERT(SOLVER, i <= s);
  Lit plit = plit_stack[s - i];
  FF_OUT(SOLVER, "ithConseq(" << i << ") returns " << to_string(plit)
	 << " with explanation " << plit2exp[plit]
	 << endl);
  return plit;
}


inline Lit Solver::ithExplain(int i) {
  FF_ASSERT(SOLVER, i >= 1);
  FF_ASSERT(SOLVER, i <= int(prop_exp.size()));
  Lit l = prop_exp[i-1];
  FF_ASSERT(SOLVER, l != Lit());
  FF_OUT(SOLVER, "ithExplain(" << i << ") returns " << to_string(l) << endl);
  return l;
}


inline const vector<Lit>&  Solver::getAssignment() const {
  return assignment;
}


inline Zp Solver::valueInSolution(const string& var) {
  auto res = solution[var];
  FF_OUT(SOLVER, var << " ~~> " << res << endl);
  return res;
}


inline int Solver::explain(Lit plit) {
  FF_ASSERT(SOLVER, plit2exp.count(plit));
  const auto& exp = plit2exp[plit];
  set<Lit> tmp(exp.begin(), exp.end());
  prop_exp = vector<Lit>(tmp.begin(), tmp.end());
  int res = prop_exp.size();
  FF_OUT(SOLVER, "explain(" << plit << ") returns " << res << endl);

#if FF_DEBUG

  if (/* false and */ true) { // Check the explanation of the propagation with Maple.

    vector<Lit> conflict = {~plit};
    for (int i = 1; i <= res; ++i)
      conflict.push_back(ithExplain(i));

    FF_ASSERT(SOLVER, inconsistent(conflict));
  }
#endif

  return res;
}


inline int Solver::check_consistency_with_non_linear_solver(int level) {
  chrono::steady_clock sc;   // create an object of `steady_clock` class
  auto start = sc.now();     // start timer

  FF_OUT(SOLVER, "Called nonlinear solver" << endl);

  int res = nonlin_solver.checkConsistency(level);

  auto end = sc.now();       // end timer (starting & ending is done by measuring the time at the moment the process started & ended respectively)
  auto time_span = static_cast<chrono::duration<double>>(end - start);   // measure time span between start & end
  time_non_linear += time_span.count();
  FF_OUT(SOLVER, "Non linear solver queries have taken: "<< time_non_linear <<" seconds "<< endl);
  return res;
}

  inline bool Solver::check_LA_model(z3::solver &z3solver) {
    using namespace z3;
    
    model m = z3solver.get_model();
    uint n = m.num_consts();
    for (uint i = 0; i < n; i++) {
      auto sc = m.get_const_decl(i);
      expr v = m.get_const_interp(sc);
      string  vn;
      if (v.is_numeral(vn)) {
        if (is_var(sc.name().str())) {
            Zp z(vn);
            solution[sc.name().str()] = z;
          }
      }
      // else {
      //   std::cout << "Value not valid: " << v << std::endl;
      //   return false;
      // }
    }
    return assignment_is_satisfied(solution);
  }

  inline int Solver::check_consistency_la(bool incremental, bool complete_deduction, bool is_leaf, bool la_over) {

  using namespace z3;
  
  // Remove information of previous iterations, restart every iteration (instead of removing inside the deductions)
  deduced_not_overflowing.clear();
  bounds.clear();
  not_overflowing_constraints.clear();
  overflowing_constraints.clear();
  not_overflowing_disjunctions.clear();


  if (complete_deduction) {
    FF_OUT(SOLVER, "Calling to complete non overflowing constraints deduction" << endl);
    compute_bounds_signals_complete(this->getAssignment(),is_leaf,la_over);
  } else {
    compute_bounds_signals(this->getAssignment(),is_leaf,la_over);
  }

  if (!is_leaf and not_overflowing_constraints.size() == 0){
    return 0;
  }
  if (not_overflowing_constraints.size() == 0 & overflowing_constraints.size() == 0) {
    return 0;
  }
  if (incremental) {
    prepare_LA_check(z3c,z3solver,true);
    // std::cout << z3solver.to_smt2() << std::endl;
    //LIACalls++;
    FF_OUT(LIA, "Calling LA solver" << endl);
    //FF_OUT(LIA, "Calling LA solver " <<  LIACalls << endl);
    //uint timeout;
    //if (LIACalls <= 4294967) {
    //if (LIACalls <= 700) {
    if (timeout < 100000) {
      timeout += 100;
    }
    z3solver.set("timeout", timeout);
    //else {
    //timeout = 4294967295;
    //timeout = 70000;
    //}
    int resla = z3solver.check();
    FF_OUT(LIA, "LA solver finished" << endl);
    if (is_leaf) std::cout << "LA solver finished in a leaf:" << resla << endl;
    else std::cout << "LA solver finished:" << resla << endl;
    if (resla == unsat) {
      //std::cout << s.to_smt2() << std::endl;
      //std::cout << s.unsat_core() << std::endl;
      //        auto a = build_FF_conflict_from_LA(s);
      //        if (a < 0) {
      //          for (auto l: conf_exp) {
      //            cout << l << endl;
      //          }
      //        }
      //FF_ASSERT(LIA, 0);
      //expr_vector core = s.unsat_core();
      FF_OUT(LIA, "LA conflict detected" << endl);
      return build_FF_conflict_from_LA(z3solver);
    }
    /*else {
      if (resla == unknown) {
        cout << "Reason: " << z3solver.reason_unknown()  << endl;
      }
      }*/
    else{
      if (la_over) {
        if (is_leaf && resla == sat) {
          // model m = z3solver.get_model();
          // cout << "SMT: " << z3solver.to_smt2()  << endl;
          // cout << "Model found: " << m.size()  << endl;
          if (check_LA_model(z3solver)) {
            cout << "LA Model is solution" << endl;
            return 0;
          } else {
            cout << "LA Model is not solution" << endl;
          }
        }
      }
    }
  } else {
    context c;
    solver s(c,"QF_LIA");
    uint timeout = 100;
    s.set("timeout", timeout);
    prepare_LA_check(c,s,false);
    //std::cout << s.to_smt2() << std::endl;
    FF_OUT(LIA, "Calling LA solver" << endl);
    int resla = s.check();
    std::cout << "LA solver finished:" << resla << endl;
    if (resla == unsat) {
       FF_OUT(LIA, "LA conflict detected" << endl);
      return build_FF_conflict_from_LA(s);
    }
    else{
      if (la_over) {
        if (is_leaf && resla == sat) {
          //cout << "Model found" << endl;
          if (check_LA_model(s)) {
            cout << "LA Model is solution" << endl;
            return 0;
          } else {
            cout << "LA Model is not solution" << endl;
          }
        }
      }
    }
  }
  return 1;
}


} // namespace FF

#endif // FF_SOLVER_INLINES_HPP

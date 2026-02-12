#ifndef FF_SOLVER_DEFS_HPP
#define FF_SOLVER_DEFS_HPP

#include "../common/commonTypes.hpp"
#include "Global.hpp"
#include "Zp.hpp"

#include "Constraint_database.defs.hpp"
#include "Linear_solver.defs.hpp"
#include "Nonlinear_solver.defs.hpp"
#include "../SolverLA/Solver.defs.hpp"
#include "z3++.h"

#include "Square_rooter.hpp"
#include "Propagator.hpp"

// The Var are the Lit without the polarity (positive or negative)
// ALL OF THE ARE POSITIVE --> BOUNDS ONLY DEDUCED FROM POSITIVE LITERALS
struct BoundsInfo {
  mpz_class min;
  mpz_class max;
  set<Var> min_deduced_from;
  set<Var> max_deduced_from;

};

typedef map<int, BoundsInfo> Bounds;

class SATSolver;

namespace FF {

using Lit = ::Lit;

class    Linear_solver;
class Nonlinear_solver;


////////////////////////
///// CLASS Solver /////
////////////////////////

// Class for solver of Finite Fields.

class Solver {

public:

  friend class    Linear_solver;
  friend class Nonlinear_solver;
  friend class LA::Solver;
  
  Solver(::SATSolver* s);
  ~Solver();

  // Needed because when solver is created, termsDB is not initialized in the SAT solver
  void notifyTermsDataBase(::TermsDB* db);

  // Returns literal representing t:
  //    *   If t is T-equivalent to TRUE,  returns Lit(1, true).
  //    * Elif t is T-equivalent to FALSE, returns Lit(1, false).
  //    * Elif t is T-equivalent to [the negation] of a previously
  //      abstracted literal, returns [the negation of] that.
  //    * Else returns Lit(p, true)
  Lit abstractLiteral(TermsDB &DB, Term t, int p);

  bool containsAbstractedEquality(const Polynomial<Zp> & eq);


  // Initializes solver once parsing is completed.
  void initializeAfterParsing();

  // Adds literal l to current assignment.
  void setTrue(Lit l);

  // Checks consistency of literals with precision level:
  //
  // - If level == 0:     leaf node of the search tree
  // - If level == 1: internal node of the search tree
  //
  // The returned value means:
  //
  //   * n < 0  =>  UNSAT    (-n == size of an inconsistent set of lits).
  //   * 0      =>  SAT
  //   * 1      =>  UNKNOWN
  //   * 2      =>  UNSOLVED (unknown, but inferred and added new clauses)
  //
  int checkConsistency(int level);

  // Returns i-th element of the inconsistent set of lits (1 <= i <= n,
  // where -n < 0 is the value returned by checkConsistency).
  Lit ithInconsist(int i);

  // Performs theory propagate with precision level and
  // returns the number of detected consequences.
  int theoryPropagate(int level);

  // Returns the i-th consequence (1 <= i <= n,
  // where n is the value returned by theoryPropagate).
  Lit ithConseq(int i);

  // Returns the size of an explanation for literal l.
  int explain(Lit l);

  // Returns the i-th element of the explanation (1 <= i <= n,
  // where n is the value returned by the last call of explain.
  Lit ithExplain(int i);

  // Sets a backtrack point.
  void setBTPoint();

  // Retract last n backtrack points.
  void backtrack(int n);


  // Returns the number of finite field variables in the formula.
  int get_num_vars() const;

  // Returns wheter name is the identifier of a variable.
  bool is_var(string name) const;

  // Given string var, returns value assigned to it in a solution.
  // Assumes var is a variable, the system of constraints is
  // satisfiable and nothing is pending to be checked for consistency.
  Zp valueInSolution(const string& var);

  // Returns the polynomial q associated to a propositional variable p
  // (p means q == 0, ¬p means q != 0).
  const Polynomial<Zp>& getPolynomial(int p) const;

  // Solution (if the formula is satisfiable). //public by now
  map<string, Zp> solution;

  // Returns the literals that are true in the current assignment.
  const vector<Lit>&  getAssignment() const;

  Square_rooter rooter;

  bool assignment_is_satisfied(const map<string, Zp>& solution);

private:

  ///////////////
  // FUNCTIONS //
  ///////////////

  // Internal implementation of checkConsistency.
  int check_consistency(int level);
  

  // Returns a textual description of l as a literal and as a constraint.
  string to_string(Lit l);

  bool inconsistent(const vector<Lit>& conflict);
  
  // Processes a new clause.
  // If the clause...
  // - is false                            -> it is handled as a conflict           (and returns -size)
  // - propagates an undefined literal     -> it is handled as a theory propagation (and returns 0)
  // - has at least two undefined literals -> it is added as a new clause           (and returns 1)
  // - is true                             -> do nothing                            (and returns 2)
  int process_new_clause(const vector<Lit>& clause);
  
  // The returned value res means:
  //
  // - if res  < 0, then a conflict of size -res has been found
  //   (and has been added to conf_exp)

  // - if res  > 0, then res literals can be propagated
  //   (and the propagated literals and their explanations have been added to plit_stack and plit2exp)

  // - if res == 0, inferred is true iff
  //   some clause with at least two undefined literals was inferred (and has been added to the formula).
  //
  int linear_clause_inference_simple(int level, bool& inferred);

  // More complete version of the analysis -> performs constant propagation
  // The returned value res means:
  //
  // - if res  < 0, then a conflict of size -res has been found
  //   (and has been added to conf_exp)

  // - if res  > 0, then res literals can be propagated
  //   (and the propagated literals and their explanations have been added to plit_stack and plit2exp)

  // - if res == 0, inferred is true iff
  //   some clause with at least two undefined literals was inferred (and has been added to the formula).
  //
  int linear_clause_inference_complete(int level, bool& inferred);

  // Auxiliar function to add clauses
  Lit generate_x_equals_value(int signal, Zp value);

  pair<Lit, bool> generate_literal_from_polynomial(const Polynomial<Zp> & pol);
  Term generate_term_from_polynomial(const Polynomial<Zp> & pol);


  // Same interface as linear_clause_inference.
  int performDeductionsFromPolynomial(const Polynomial<Zp> & pol, const vector<Lit> & lit_pol, bool& inferred);
  
  //void preprocess_info_constraints(const vector<Lit> & polynomials);

  void compute_bounds_signals(const vector<Lit> & polynomials, bool is_leaf, bool la_over);

  void compute_bounds_signals_complete(const vector<Lit> & polynomials, bool is_leaf, bool la_over);

  bool check_LA_model(z3::solver &z3solver);
  
  void prepare_LA_check(z3::context &c, z3::solver &s, bool incremental);

  int build_FF_conflict_from_LA(z3::solver &s);

  int check_consistency_light();
  int check_consistency_with_non_linear_solver(int level);
  int check_consistency_la(bool incremental, bool complete_deduction, bool is_leaf, bool la_over);


  ////////////
  // FIELDS //
  ////////////

  // Database of equalities and disequalities.
  Constraint_database cons_db;

  ::SATSolver*            engine; // Needed for adding clauses dynamically.

  //LA::Solver           la_solver;
  Linear_solver       lin_solver;
  Nonlinear_solver nonlin_solver;

  // Stack of literals set to true.
  // Backtrack points are marked with a Lit() lit
  // (which is not a valid literal).
  vector<Lit> assignment;

  //  // Solution (if the formula is satisfiable).
  //  map<string, Zp> solution;

  // Studied set of combinations of literals, to do not repeat efforts
  set<vector<uint>> studied_polynomials;

  // Map from signals to the polynomials in which they appear
  map<int, vector<uint>> signal_to_polynomials;

  // Map from the polynomials to the signals that they contain
  map<uint, set<int>> polynomial_to_signals;

  // Map from the polynomials to the single signals that they contain
  // A single signal is a signal that appears only in the linear part with coef 1 or -1
  map<uint, set<int>> polynomial_to_single_signals;

  // To measure the time used by the non linear solver
  double time_non_linear;
  
  // Stack of propagated literals.
  // Backtrack points are marked with a Lit(1, true) lit
  // (which should never be truly theory propagated).
  vector<Lit> plit_stack;

  // Points to next literal in plit_stack to notify when theoryPropagate is called.
  int next;

  // Map of explanations of propagated literals.
  map<Lit, vector<Lit>> plit2exp;

  vector<Lit> conf_exp; // Literals that explain the last conflict.
  vector<Lit> prop_exp; // Literals that explain the propagated literal that was last queried.


  /*
  struct BoundsInfo {
    mpz_class min;
    mpz_class max;
    set<Var> deduced_from;

    // AÑADIR A UN EXPLAIN MIN Y EXPLAIN MAS QUE SEAN DISTINTOS
  };

  typedef map<int, BoundsInfo> Bounds;
  */
  
  // Dynamic!!! Depend on the assignment
  // The vars explaining are always positive --> turn to positive when building lit
  Bounds bounds;
  vector<pair<Lit, set<Var>>> not_overflowing_constraints;
  vector<Lit> overflowing_constraints;
  vector<pair<Polynomial<Zp>, set<Var>>> deduced_not_overflowing;
  vector<pair<vector<Polynomial<Zp>>, Var>> not_overflowing_disjunctions; 


  //uint LIACalls;
  uint timeout;

  z3::context z3c;
  //z3::simplifier simp;
  z3::solver z3solver;
  //z3::params z3p;
  map<string, set<Var>> Z3FFLiteralRelation;
  map<string, Lit> Z3FFnegativeLiterals;

}; // End of class Solver.

} // namespace FF

#endif // FF_SOLVER_DEFS_HPP


/*

  Dynamic clause addition
  =======================

  Class ClauseDataBase from

  smtSystem/arithmeticSolver/dpllx/clauseDataBase.h

  has methods:

  void   addLiteralToNewClause(Lit lit);

  and

  Clause addNewClause(uint act, bool isInput,uint id);

  where

  act: initial activity (ClauseObject::infActivity for input clauses, 0 for lemmas, )
  isInput: true iff input clause (only lemmas can be removed at clause cleanups)
  id: only meaningful in proof mode; otherwise can be 0

  Examples where these methods are used: in smtSystem/arithmeticSolver/dpllx/SATSolver.cpp, lines 765-781 and 789-840

  These methods can be accessed from the finite field solver as follows.

  In class FF::Solver from
  smtSystem/arithmeticSolver/SolverFF/Solver.defs.hpp
  the field engine has type ::SATSolver*.

  And class SATSolver from
  smtSystem/arithmeticSolver/dpllx/SATSolver.h
  has a field clauseDB of type ClauseDataBase.


  Dynamic atom creation
  =====================

  Class ArithmeticSolver from

  smtSystem/arithmeticSolver/arithmeticSolver.defs.hpp

  has a method

  pair<Lit, bool> abstractTheoryAtom(Term atom);

  that notifies that atom (an equality) is a term of the theory
  (as if atom had been present in the input formula at parsing time).
  Returns the pair of the corresponding literal, and true iff the atom is new.

  In class FF::Solver from
  smtSystem/arithmeticSolver/SolverFF/Solver.defs.hpp
  the field engine has type ::SATSolver*.
  And class SATSolver from
  smtSystem/arithmeticSolver/dpllx/SATSolver.h
  has a field arithmeticSolver of type ArithmeticSolver*

  If the atom is new, then it has to be notified to the linear solver. Class Linear_solver has a method

  void defineNewEquality(int p, const Polynomial<Zp>& q);

  which tells the linear solver that propositional variable p is the
  abstraction of the polynomial equality q == 0.

  The polynomial corresponding to propositional variable p can be recovered by calling:

  cons_db.polynomial(p)

  We may also need a function for transforming an object of class
  Polynomial into an object of class Term meaning the syntactical
  representation of the (normalized) polynomial. Class TermsDB from
  smtSystem/arithmeticSolver/termsDB can be used for that.
*/

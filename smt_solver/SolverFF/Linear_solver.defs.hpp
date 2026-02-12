#ifndef FF_LINEAR_SOLVER_DEFS_HPP
#define FF_LINEAR_SOLVER_DEFS_HPP

#include "../common/commonTypes.hpp"
#include "Global.hpp"
#include "Zp.hpp"
#include "F_matrix.defs.hpp"
#include "C_matrix.defs.hpp"
#include "Basis.defs.hpp"


namespace FF {

using Linear_expression = vector< pair<int, Zp> >; // 1st: variable; 2nd: coefficient.


// Class for representing constraints of the form x = k, x != k, where x is a variable, k a value.
struct Domain_constraint {

  int  variable;
  bool equal;
  Zp   value;

  vector<Lit> exp; // The conjunction of the literals in the explanation implies the constraint.

  // Default constructor gives an invalid object, to be used as a mark for backtracking.
  bool valid() const { return variable != WRONG_INDEX; }

  Domain_constraint() : variable(WRONG_INDEX), equal(), value(), exp() { }

  Domain_constraint(int variable, bool equal, const Zp& value, const vector<Lit>& exp) :
    variable  (variable),
    equal     (equal),
    value     (value),
    exp       (exp) { }
};


class Solver;


class Linear_solver {

public:

  Linear_solver(Solver& s);
  ~Linear_solver();

  // Initializes solver once parsing is completed.
  void initializeAfterParsing();

  // Defines a new equality q == 0 (whose abstraction is the propositional variable p)
  // that can later be set to true or false.
  void defineNewEquality(int p, const Polynomial<Zp>& q);

  // Asserts literal l.
  void setTrue(Lit l);

  // Checks consistency of asserted literals with precision level.
  //
  // level == 0: leaf of the search tree.
  // level == 1: internal node.
  //
  // Returns:
  //
  //    * 0      =>  SAT
  //    * 1      =>  UNKNOWN
  //    * n < 0  =>  UNSAT    (-n == size inconsistent set of lits).
  //
  // If level == 1 then 0 may be returned even though the set is UNSAT actually.
  //
  int checkConsistency(int level);

  // Performs theory propagation of asserted literals with precision level.
  //
  // level == 0: leaf of the search tree.
  // level == 1: internal node.
  //
  // Returns:
  //
  //    * n >= 0 =>  n literals can be propagated (if level == 0 then n == 0)
  //    * n <  0 =>  UNSAT    (-n == size inconsistent set of lits).
  //
  int theoryPropagate(int level);

  // Sets a backtrack point.
  void setBTPoint();

  // Retract last n backtrack points.
  void backtrack(int n);


private:

  ///////////////
  // FUNCTIONS //
  ///////////////

  // Abstraction
  //////////////

  // A (finite field) variable may be:
  //
  // - original
  //
  // - auxiliary
  //
  //     - an abstraction of a monomial ("monomial variable")
  //     - an abstraction of a linear expression ("linear expression variable")
  //
  // Returns the number of all variables (original + auxiliary).
  int number_variables();

  bool          is_original_variable(int v);
  bool          is_monomial_variable(int v);
  bool is_linear_expression_variable(int v);

  // Returns the (identifier of the auxiliary) variable ...
  int variable(const          Monomial& mon); // ... of a monomial.
  int variable(const Linear_expression& lin); // ... of a linear expression.

  // The inverses of the two previous functions.
  const          Monomial&          monomial(int v);
  const Linear_expression& linear_expression(int v);


  // Consistency
  //////////////

  // Assert an equality / a disequality. Returns if constraint is new.
  bool assert_equality   (int x, const Zp& k, const vector<Lit>& exp);
  bool assert_disequality(int x, const Zp& k, const vector<Lit>& exp);
  
  // Checks domain constraint with index idx in the trail.
  int check_domain_constraint(int idx);

  // In the current solution,
  // sets the value of non-basic variable xn to val and updates the values of all basic variables.
  void update(int xn, const Zp& val);

  // Returns iterator pointing at a checked occurrence of x == * in the list of (indices of) equalities eq,
  // or eq.end() if there is none.
  vector<int>::const_iterator find_equality(const vector<int>& eq);
  
  // Returns iterator pointing at a checked occurrence of x != k in the list of (indices of) disequalities dis,
  // or dis.end() if there is none.
  vector<int>::const_iterator find_disequality(const vector<int>& dis, const Zp& k);

  // Composes a conflict explanation by joining the literals in lits and others.
  // Returns -size of the resulting explanation (the value to be returned by checkConsistency).
  int make_conflict_explanation(const vector<Lit>& v_lits, const vector<Lit>& others);

  // Returns a non-basic variable with non-zero coefficient in row r
  // which is not fixed (i.e., does not have any equalities in its domain constraints).
  // Returns WRONG_INDEX if there are none.
  int find_non_basic_non_fixed_variable_in_row(int r);

  // Find the largest one.
  int find_largest_non_basic_non_fixed_variable_in_row(int r);

  // Makes a heavy consistency check.
  int check_consistency_heavy();

  // Returns if solution is compatible with the semantics of nonlinear monomials.
  bool solution_compatible_with_nonlinear_monomials();


  // Propagation
  //////////////

  // Propagates domain constraint with index idx in the trail.
  int propagate_domain_constraint(int idx);

  // Notifies to the SAT solver that domain constraint is implied.
  int notify_propagation(int x, bool eq, const Zp& k, const vector<Lit>& exp);


  // Debugging
  ////////////

  void print_solution(); // Prints current solution.

  bool solution_satisfies_equalities();
  bool solution_satisfies_domain_constraints_of_variable(int x);
  bool solution_satisfies_domain_constraints_of_non_basic_variables();
  bool solution_satisfies_domain_constraints_of_basic_variables();

  bool ok();

  string to_string(int x);
  string to_string(const Domain_constraint& uc);


  ////////////
  // FIELDS //
  ////////////

  Solver& s;


  // Abstraction
  //////////////

  // Map (identifier of monomial) --> monomial, and its inverse.
  // The identifier of a monomial is called its index
  // (to avoid confusions with the identifier of a linear expression).
  vector<Monomial>   idx2mon;
  map<Monomial, int> mon2idx;

  // Map (identifier of linear expression) --> (linear expression), and its inverse.
  // The identifier of a linear expression is called its position
  // (to avoid confusions with the identifier of a monomial).
  vector<Linear_expression>   pos2lin;
  map<Linear_expression, int> lin2pos;

  // Identifiers of monomial and linear expression variables are intertwined,
  // and have values beyond those of original variables.
  //
  // The identifier of an auxiliary variable (monomial or linear expression variable) is
  // its rank (at rnk2idx_pos, see below) + the number of original variables.
  // For each monomial and linear expression there is an item in rnk2idx_pos.
  vector<pair<int, bool>> rnk2idx_pos; // 1st field: index of monomial / position of linear expression;
				       // 2nd field: true if monomial, false if linear expression.
  vector<int>                 idx2rnk; // Map (index of monomial)             --> (rank at rnk2idx_pos)
  vector<int>                 pos2rnk; // Map (position of linear expression) --> (rank at rnk2idx_pos)

  // If p is a propositional variable that abstracts the polynomial equality q == k,
  // where k is a constant and q is a polynomial without constant term:
  map<int, Zp > pvar2cns; // pvar2cns[p] = k
  map<int, int> pvar2var; // pvar2var[p] = x,
			  // where x is the (identifier of the auxiliary) variable
			  // of the linear expression that abstracts (the monomials in) polynomial q.

  // Maps a variable x to the propositional variables p1, ..., pn s.t.
  // p1, ..., pn are the boolean abstractions of the equalities of the form x == k.
  vector< vector<int> > var2pvars;


  // Consistency
  //////////////

  // F_matrix* tableau;
  C_matrix* tableau;
  Basis*    basis;

  // Current solution, i.e.,
  // assignment of finite field values to original + auxiliary variables satisfying checked literals.
  vector<Zp> sol;

  // Trail of asserted domain constraints.
  vector<Domain_constraint> trail;
  
  vector< vector<int> > equals_to; // x -> { indices in trail of    equalities of the form x == k }
  vector< vector<int> > diff_from; // x -> { indices in trail of disequalities of the form x != k }

  int next_chck; // Position of the next literal in the trail to be checked for consistency.


  // Propagation
  //////////////

  int next_prop; // Position of the next literal in the trail to be propagated.

  // Matrix of the initial tableau, for theory propagation.
  C_matrix* initial;

  // var2indices[x] is the list of indices of monomials m such that original variable x occurs in m.
  vector< vector<int> > var2indices;

  // idx2cnt[i] counts for the monomial with index i the number of non-fixed variables in it.
  // When this number is equal to 0, then the monomial can be evaluated.
  vector<int> idx2cnt;

  // row2cnt[r] counts for the row r of the initial matrix the number of non-fixed variables in it.
  // When this number is equal to 1, then an equality can be propagated.
  vector<int> row2cnt;
};

}

#endif // FF_LINEAR_SOLVER_DEFS_HPP

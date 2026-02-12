#ifndef FF_NONLINEAR_SOLVER_DEFS_HPP
#define FF_NONLINEAR_SOLVER_DEFS_HPP

#include "../common/commonTypes.hpp"
//#include "Polynomial.hpp"

#include "Global.hpp"
#include "Zp.hpp"
#include "maplec.h"
//#include <CoCoA/ring.H>
//#include <CoCoA/BigInt.H>

namespace FF {

class Solver;

void literal2maple_pol(ostringstream& result, const Solver& s, Lit lit, set<string> & variables);

class Nonlinear_solver {

public:

  Nonlinear_solver(Solver& s, bool apply_nra, bool using_cocoa);

  ~Nonlinear_solver();
  // Transforms polynomials in s.assignment to CoCoA::RingElem
  //void literals2cocoa_pols(std::vector<CoCoA::RingElem>& generators);

  std::pair<std::string, std::set<std::string>> literals2maple_pols();

  // Initializes solver once parsing is completed.
  void initializeAfterParsing();

  // Checks consistency of literals with precision level.
  //
  // If level == 0 (leaf of the search tree) returns:
  //    * 0      =>  SAT
  //    * 1      =>  UNKNOWN
  //    * n < 0  =>  UNSAT    (-n == size inconsistent set of lits).
  //
  // If level == 1 (internal node) then 0 may be returned even though the set is UNSAT actually.
  int checkConsistency(int level);

    int checkConsistency_maple(int level);  

    int checkConsistency_cocoa(int level);

  // Sets a backtrack point.
  void setBTPoint();
  
  //It initializes a maple session if maple_initialized == false.
  void initialize_maple();

  // Retract last n backtrack points.
  void backtrack(int n);


  string produce_test_polynomials(int level);
  void test();

private:

  Solver&       s;
  MKernelVector kv;
  int num_queries;
  bool using_maple = false;
  bool maple_initialized = false;
  bool firstSATNRA = false;
//const CoCoA::BigInt& PRIME;

  //  bool get_model_in_NRA(vector<Polynomial<FF::Zp>> basis);
  
};

}
 
#endif // FF_NONLINEAR_SOLVER_DEFS_HPP

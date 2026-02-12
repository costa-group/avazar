#ifndef FF_GLOBAL_HPP
#define FF_GLOBAL_HPP

#include <iostream>
#include <fstream>
#include <sstream>
#include <utility>
#include <vector>
#include <set>
#include <map>
#include <tuple>
#include <unordered_set>
#include <unordered_map>
#include <algorithm>
#include <numeric>
#include <functional>
#include <assert.h>
#include <limits.h>
#include <math.h>
#include <gmpxx.h>
#include <chrono>


using namespace std;

namespace FF {

////////////////////////////////////////////////////////////////

template<typename T>
ostream& operator<< (ostream& out, const vector<T>& v) {
  for (T x : v) out << '\t' << right << x;
  return out;
}

////////////////////////////////////////////////////////////////

// Invalid index for an array, invalid variable/row/column, etc.
const int WRONG_INDEX = -1; 

////////////////////////////////////////////////////////////////

class Context;
extern Context* p_ctxt;

////////////////////////////////////////////////////////////////

struct Options {

  bool apply_la_incremental;
  bool apply_nra;
  bool using_cocoa;

  int light_check_determinism;
  int apply_la;
  int linear_solver;  
  int simple_deductions;
  int complete_deductions;
  int complete_non_overflowing_deductions;
  int la_with_overflowing_constraints;

  
  Options() :                 // Default values.

    apply_la_incremental    (true),
    using_cocoa             (true),
    apply_nra               (true),
    light_check_determinism (1),
    apply_la                (1),
    linear_solver           (1),
    simple_deductions       (1),
    complete_deductions     (0),
    complete_non_overflowing_deductions    (1), 
    la_with_overflowing_constraints   (0) { }
};

// For code readability.
#define FIRE(x)								\
  (engine->arithmeticSolver->options.x != 0 and				\
   check_consistency_counter % engine->arithmeticSolver->options.x == 0)

////////////////////////////////////////////////////////////////

// Tags for locally switching on/off debugging/printing.
enum Tag {
  SOLVER,
  LIA,
  CONSTRAINT_DATABASE,
  LINEAR,
  NONLINEAR,
  MONOMIAL,
  POLYNOMIAL,
  ZP,
  CONTEXT,
  F_MATRIX,
  C_MATRIX,
  BASIS,
  INT_SET,
  VEC,
  PROPAGATOR
};

// Returns if tag is active for debugging/printing.
inline bool active(Tag t) {

  switch(t) {
  case SOLVER                  : return true;
  case LIA                     : return false;
  case CONSTRAINT_DATABASE     : return false;
  case LINEAR                  : return false;
  case NONLINEAR               : return false;
  case MONOMIAL                : return false;
  case POLYNOMIAL              : return false;
  case ZP                      : return false;
  case CONTEXT                 : return false;
  case F_MATRIX                : return false;
  case C_MATRIX                : return false;
  case PROPAGATOR              : return false;

  default                      : return false;
  }
}

////////////////////////////////////////////////////////////////

///////////////
// DEBUGGING //
///////////////

// Switch on/off debugging.
// #define FF_DEBUG true
#define FF_DEBUG false


// Code to be run only in debugging mode.
#if FF_DEBUG 
#define FF_DEBUG_CODE(S)   S
#else
#define FF_DEBUG_CODE(S)   ;
#endif


// Like assert, but can be locally switched on/off with tags.
#if FF_DEBUG
#define FF_ASSERT(tag, cond)  if (FF::active(tag))  assert( (cond) );
#else
#define FF_ASSERT(tag, cond)  ;
#endif
  
////////////////////////////////////////////////////////////////

//////////////
// PRINTING //
//////////////

// Switch on/off printing.
// #define FF_PRINT true
#define FF_PRINT false

// Like cout, but can be locally switched on/off with tags.
#if FF_PRINT
#define FF_OUT(tag, output)  { if (FF::active(tag)) cout << output; }
#else
#define FF_OUT(tag, output)  ;
#endif

////////////////

// If off,
// products in monomials and polynomials are made explicit by printing '*'.
extern bool pretty_printing_on;

////////////////////////////////////////////////////////////////

} // namespace FF
  
#endif // FF_GLOBAL_HPP

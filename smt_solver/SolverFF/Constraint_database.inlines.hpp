#ifndef FF_CONSTRAINT_DATABASE_INLINES_HPP
#define FF_CONSTRAINT_DATABASE_INLINES_HPP

#include "Constraint_database.defs.hpp"
#include "Solver.inlines.hpp"

namespace FF {


inline Constraint_database::Constraint_database() { }


inline Lit Constraint_database::
abstract_equality(TermsDB &DB, Term eq, int pvar) {
  Polynomial<Zp> q;
  parse_equality_as_polynomial(DB, eq, q);
  Lit lit = abstract_equality(q, pvar);
  FF_OUT(CONSTRAINT_DATABASE,
	 "Abstraction of " << DB.term2string(eq)
	 << ": literal " << lit
	 << ", polynomial " << q << " == 0" << endl);
  return lit;
}


inline Lit Constraint_database::
abstract_equality(const Polynomial<Zp>& q, int pvar) {

  Lit lit;
  if                  (is_zero(q)) lit = Lit(1,  true);
  else if (is_nonzero_constant(q)) lit = Lit(1, false);
  else {
    auto [it1, added1] = poly2pvar.insert({q, pvar});
    if (added1) {
#if FF_DEBUG      
      auto [it2, added2] =
#endif	
	pvar2poly.insert({pvar, q});
      FF_ASSERT(CONSTRAINT_DATABASE, added2);      
    }
    lit = Lit(it1->second, true);
  }
  return lit;
}

inline bool Constraint_database::
contains_abstracted_equality(const Polynomial<Zp>& q){
  return poly2pvar.count(q) != 0;
}



inline void Constraint_database::
parse_equality_as_polynomial(TermsDB &DB, Term eq, Polynomial<Zp>& q) {

  FF_ASSERT(CONSTRAINT_DATABASE, is_zero(q));
  FF_ASSERT(CONSTRAINT_DATABASE, DB.topSymbol(eq) == "=");
  FF_ASSERT(CONSTRAINT_DATABASE, DB.arity(eq) == 2);

  Polynomial<Zp> lhs;
  Polynomial<Zp> rhs;
  parse_expression_as_polynomial(DB, DB.ithChild(eq, 0), lhs);
  parse_expression_as_polynomial(DB, DB.ithChild(eq, 1), rhs);
  q = lhs + (Zp(-1) * rhs);
  if (not is_zero(q)) q.normalize();
}


} // using namespace FF

#endif // FF_CONSTRAINT_DATABASE_INLINES_HPP

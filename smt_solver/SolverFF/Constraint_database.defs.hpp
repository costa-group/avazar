#ifndef FF_CONSTRAINT_DATABASE_DEFS_HPP
#define FF_CONSTRAINT_DATABASE_DEFS_HPP

#include "../common/commonTypes.hpp"
#include "../termsDB/termsDB.inlines.hpp"

#include "Zp.hpp"
#include "Polynomial.hpp"

namespace FF {

using Lit = ::Lit;


// Parses expr and returns:
//  o true      if it is a finite field number (and x is set to this number),
//  o false     otherwise                      (and x may take any value).
bool parse_number(TermsDB &DB, Term expr, Zp& x);


///////////////////////////////////
//// CLASS Constraint_database ////
///////////////////////////////////

// Class for parsing and storing database of constraints.

class Constraint_database {

  using Const_Iterator = map<int, Polynomial<Zp>>::const_iterator;
  
public:

  Constraint_database();


  // Returns literal representing equality eq (as a term or as a polynomial):
  //    *   If eq is T-equivalent to TRUE,                returns Lit(1, true).
  //    * Elif eq is T-equivalent to FALSE,               returns Lit(1, false).
  //    * Elif eq is T-equivalent to a previous equality, returns its literal.
  //    * Else                                            returns Lit(p, true).
  Lit abstract_equality(TermsDB &DB,     Term eq, int p);
  Lit abstract_equality(const Polynomial<Zp>& eq, int p);

  bool contains_abstracted_equality(const Polynomial<Zp>& eq);


  // Returns polynomial (of the equality) of the propositional variable pvar.
  const Polynomial<Zp>& polynomial(int pvar) const {
    FF_ASSERT(CONSTRAINT_DATABASE, pvar2poly.count(pvar));
    return pvar2poly.at(pvar);
  }

  // Returns the number of finite field variables in the formula. 
  int get_num_vars() const {
    return ctxt.get_num_vars();
  }

  // Returns the identifier of a variable.
  int identifier(string name) {
    return ctxt.name_to_index().at(name);
  }
  
  // Returns wheter name is the identifier of a variable.
  bool is_var(string name) {
    return ctxt.name_to_index().find(name) != ctxt.name_to_index().end();
  }
  
  Const_Iterator  begin() const { return pvar2poly.cbegin(); }
  Const_Iterator    end() const { return pvar2poly.  cend(); }

  // Returns the number of atoms in the theory of finite fields.
  int size() const { return pvar2poly.size(); }


private:

  ///////////////
  // FUNCTIONS //
  ///////////////

  // Sets the polynomial p so that expression is equivalent to p.
  void parse_expression_as_polynomial(TermsDB &DB, Term expression, Polynomial<Zp>& p);

  // Sets the polynomial p so that equality is equivalent to p == 0.
  void parse_equality_as_polynomial  (TermsDB &DB, Term equality,   Polynomial<Zp>& p);


  ////////////
  // FIELDS //
  ////////////

  // Manages the bijection between finite field variables and their names.
  Context ctxt;

  map<Polynomial<Zp>, int> poly2pvar; // polynomial -> propositional variable.
  map<int, Polynomial<Zp>> pvar2poly; // propositional variable -> polynomial.

}; // End of class Constraint_database.

} // using namespace FF

#endif // FF_CONSTRAINT_DATABASE_DEFS_HPP

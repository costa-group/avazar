#include "Constraint_database.inlines.hpp"
#include "../termsDB/termsDB.defs.hpp"
#include "../termsDB/termsDB.inlines.hpp"

using namespace FF;
 

bool FF::parse_number(TermsDB &DB, Term expr, Zp& x) {

  const string& s = DB.topSymbol(expr);
  switch (s[0]) {

  case '+'   : {
    x = 0;
    Zp y;
    for (int k = 0, arity = DB.arity(expr); k < arity; k++)
      if (parse_number(DB, DB.ithChild(expr, k), y))
	x += y;
      else
	return false;

    return true;
  }

  case '-'   : {
    Zp y;
    if (parse_number(DB, DB.ithChild(expr, 0), x) &&
	parse_number(DB, DB.ithChild(expr, 1), y)) {
      y *= -1;
      x += y;
      return true;
    }
    else
      return false;
  }

  case '*'   : {
    Zp y;
    if (parse_number(DB, DB.ithChild(expr, 0), x) &&
	parse_number(DB, DB.ithChild(expr, 1), y)) {
      x *= y;
      return true;
    }
    else
      return false;
  }

  case '/': {
    Zp y;
    if (parse_number(DB, DB.ithChild(expr, 0), x) &&
	parse_number(DB, DB.ithChild(expr, 1), y)) {
      x = x / y;
      return true;
    }
    else
      return false;
  }

  case '~':
    if (parse_number(DB, DB.ithChild(expr, 0), x)) {
      x *= -1;
      return true;
    }
    else
      return false;

    // Number.
  case '0':   case '1':   case '2':   case '3':   case '4':
  case '5':   case '6':   case '7':   case '8':   case '9':
    x = Zp(s);
    return true;

  default:
    return false;
  }
}


void Constraint_database::
parse_expression_as_polynomial(TermsDB &DB, Term expr, Polynomial<Zp>& p) {

  FF_ASSERT(CONSTRAINT_DATABASE, is_zero(p));
  
  const string& s = DB.topSymbol(expr);
  switch (s[0]) {

  case '+'   : 
    for (int k = 0, arity = DB.arity(expr); k < arity; k++) {
      Polynomial<Zp> q;
      parse_expression_as_polynomial(DB, DB.ithChild(expr, k), q);
      p = p + q;
    }
    break;

  case '-'   : {
    Polynomial<Zp> q;
    parse_expression_as_polynomial(DB, DB.ithChild(expr, 0), p);
    parse_expression_as_polynomial(DB, DB.ithChild(expr, 1), q);
    q = Zp(-1) * q;
    p = p + q;
    break;
  }
    
  case '~'   :
    parse_expression_as_polynomial(DB, DB.ithChild(expr, 0), p);
    p = Zp(-1) * p;
    break;

  case '*'   : {
    Polynomial<Zp> q;
    parse_expression_as_polynomial(DB, DB.ithChild(expr, 0), p);
    parse_expression_as_polynomial(DB, DB.ithChild(expr, 1), q);
    p = p * q;
    break;
  }
    
  case '0':  case '1':  case '2':  case '3':  case '4':
  case '5':  case '6':  case '7':  case '8':  case '9': {
    Zp num;    
    parse_number(DB, expr, num);
    if (is_zero(num)) p = Polynomial<Zp>();
    else              p = Polynomial<Zp>(num, Monomial());
    break;
  }
    
  case '/'   : {
    Zp num;
    bool ok = parse_number(DB, DB.ithChild(expr, 1), num);
    assert(ok); // assert but not FF_ASSERT to avoid compilation warnings.
    Zp inv = Zp(1) / num;
    parse_expression_as_polynomial(DB, DB.ithChild(expr, 0), p);
    p = inv * p;
    break;
  }
    
  default    :                // Finite field variable.
    int ind = ctxt.index(s);
    FF_ASSERT(CONSTRAINT_DATABASE, ind >= 0);
    p = Polynomial<Zp>(Zp(1), Monomial(ind));
    break;
  }  
}

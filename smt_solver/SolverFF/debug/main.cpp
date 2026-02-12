// When integrating into the SMT solver,
// these two are the only inclusions that should be added.
// See the main below as an example of usage.
// The .hpp files themselves don't need to be inspected.

#include "../Square_rooter.hpp"
#include "../Propagator.hpp"

////////////////////////////////////////////////////////////////

// From here till line 30 it can be ignored.
// It is needed to mimic the environment of the SMT solver.

#include <iostream>
#include <vector>

using namespace std;
using namespace FF;

//string prime = "41";
// string prime = "101";
// string prime = "46337";
// string prime = "2147483647";
// string prime = "4294967291";
string prime = "21888242871839275222246405745257275088548364400416034343698204186575808495617";

mpz_class Zp::p;
mpz_class Zp::h;

////////////////////////////////////////////////////////////////

// The main shows how to use the propagator on a sample of polynomials.

int main() {

  // From here till line 71 it can be ignored.
  // It is needed to mimic the environment of the SMT solver
  // and to build the polynomials of the examples.
  
  Zp::p = mpz_class(prime.c_str());
  Zp::h = (Zp::p - 1) / 2;

  Context ctxt;

  // Variables as identifiers.
  int x_ = ctxt.index("x");
  int y_ = ctxt.index("y");
  int z_ = ctxt.index("z");
  int u_ = ctxt.index("u");
  int v_ = ctxt.index("v");
  int w_ = ctxt.index("w");

  // Variables as monomials.
  Monomial one;
  Monomial x__(x_, 1);
  Monomial y__(y_, 1);
  Monomial z__(z_, 1);
  Monomial u__(u_, 1);
  Monomial v__(v_, 1);
  Monomial w__(w_, 1);

  // Variables as polynomials.
  using Poly = Polynomial<Zp>;
  Poly x(1, x__);
  Poly y(1, y__);
  Poly z(1, z__);
  Poly u(1, u__);
  Poly v(1, v__);
  Poly w(1, w__);

  ////////////////
  
  vector<Poly> polys = {

    // x*x + Poly(-2)*x*y + y*y,
    // x*x + Poly(2)*x*y + y*y + Poly(2)*x + Poly(2)*y + Poly(-3),
    // x*x + Poly(3), // If prime is 41, 3 is not a square root.
    //                // 1 == 0 means FALSE.
        
    // u*u + Poly(-1)*v + Poly(-1)*z,
    // x*x + Poly(-2)*x*y + y*y + Poly(-1)*z + Poly(1),
    // Poly(4)*u*u + Poly(-4)*v + Poly(-4)*z,
    
    // Poly(4)*x*y,
    // Poly(-4)*x*x + y*y,
    // x*x + Poly(-3)*y*y, // If prime is 41, 3 is not a square root.
    // Poly(-4)*x*x + y*y + Poly(-1),
    // Poly(-4)*x*x + y*y + Poly(-1)*z,
    
    // x*x + Poly(-2)*x*y + y*y + Poly(2)*y,
    // x*x + Poly(1), // If prime is 41, the square root of -1 is 9.
    // u*u + Poly(2)*u*v + v*v + Poly(-1),
    // x*x + Poly(-1)*z*z,
    // Poly(2)*x*x + Poly(2)*x*y + Poly(2)*x*z + y*y + z*z,
    // x*x + Poly(-4)*y*y + Poly(-1),
    // Poly(-1)*x*x + y + z + Poly(1),

    // x*x + y*y + z*z,
    
    // x + Poly(1),   // Nothing to contribute if polynomial is already linear.
    // Poly(4)*x*y*z, // Can only handle quadratic polynomials.
    // x*x*x,         // Can only handle quadratic polynomials.
    // Poly(3)*x*x + Poly(337396) * x + Poly(1)


    x + Poly(-1)*y + z + z*y + Poly(-1)*z*z

  };

  // Objects of class Square_rooter are used for finding square roots.
  // The same object can be shared by all, so we only need to create one.
  Square_rooter rooter; 
  
  for (const auto& q : polys) {
    cout << endl << q << " == 0" << endl;
    cout << "implies" << endl;
    Propagator prop(rooter, q);

    // A pair {q, true}  of class pair<Polynomial<Zp>, bool> means p == 0.
    // A pair {q, false} of class pair<Polynomial<Zp>, bool> means p != 0.
    // A vector of class pair<Polynomial<Zp>,bool>   means their disjunction.
    // A vector of vector<pair<Polynomial<Zp>,bool>> means their conjunction.
    vector< vector< pair<Polynomial<Zp>, bool> > > res = prop.result();
    
    // If res is empty then it represents TRUE: we propagated nothing.
    if (res.empty())
      cout << "TRUE" << endl;
    else {
      bool first_and = true;
      for (const vector< pair<Polynomial<Zp>, bool> >& v : res) {
        if (first_and) first_and = false;
        else {
          cout << "/\\" << endl;
        }
        bool first_or = true;
        for (const auto& [q, e] : v) {
          if (first_or) first_or = false;
          else {
            cout << "  \\/" << endl;
          }
          cout << "  " << q << (e ? " == " : " != ") << "0" << endl;
        }
      }
      cout << endl;
    }
  }
}

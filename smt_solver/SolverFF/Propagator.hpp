#ifndef PROPAGATOR_HH
#define PROPAGATOR_HH

#include "Zp.hpp"
#include "Monomial.hpp"
#include "Polynomial.hpp"
#include "Context.hpp"

namespace FF {

// Based on /home/erodri/Nextcloud/poly-eqs/04-12-24/notes.txt.


class Propagator {

public:


  bool is_partially_diagonalized(int i) {
    for (int j = 0; j < i; ++j)
      if (m[j][i] != 0) return false;
    return true;
  }


  Propagator(const Square_rooter& rooter, const Polynomial<Zp>& q) : rooter(rooter) {

    // 0. Transform into matrix representation, if possible.

    ok = true;

    k = 0;
    for (const auto& [mon, coe] : q) {

      if (is_one(mon)) k = coe;
      else if (is_single_signal(mon)) {
	int extn = mon.begin()->first;
	int intn = variable(extn);
	v[intn] = coe;
      }
      else {
	const int UNDEF = -1;
	int extn1 = UNDEF;
	int extn2 = UNDEF;
	for (const auto& [var, exp] : mon) {
	  if (exp > 2) {
	    ok = false;
	    break;
	  }
	  else if (exp == 2) {
	    if (extn1 == UNDEF) {
	      FF_ASSERT(PROPAGATOR, extn2 == UNDEF);
	      extn1 = extn2 = var;
	    }
	    else {
	      ok = false;
	      break;
	    }
	  }
	  else {
	    FF_ASSERT(PROPAGATOR, exp == 1);
	    if (extn1 == UNDEF) {
	      FF_ASSERT(PROPAGATOR, extn2 == UNDEF);
	      extn1 = var;
	    }
	    else if (extn2 == UNDEF) {
	      extn2 = var;
	    }
	    else {
	      ok = false;
	      break;
	    }
	  }
	}

	if (ok) {
	  FF_ASSERT(PROPAGATOR, extn1 != UNDEF and extn2 != UNDEF);
	  int intn1 = variable(extn1);
	  int intn2 = variable(extn2);
	  if      (intn1 > intn2) m[intn2][intn1] = coe / 2; // Fill only one triangle.
	  else if (intn1 < intn2) m[intn1][intn2] = coe / 2;
	  else                    m[intn1][intn2] = coe;
	}
	else break;
      }
    }

    if (ok) {

      int n = m.size();

      a = vector<vector<Zp>>(n, vector<Zp>(n, 0));
      for (int i = 0; i < n; ++i)
	a[i][i] = 1;

      b = vector<Zp>(n, 0);


      // 1. Diagonalise the matrix

      for (int i = 0; i < n; ) {

	FF_ASSERT(PROPAGATOR, is_partially_diagonalized(i-1));

	if (m[i][i] == 0) {

	  const int UNDEF = -1;
	  int j = UNDEF;
	  for (int k = i+1; k < n; ++k) {
	    if (m[i][k] != 0) {
	      j = k;
	      break;
	    }
	  }
	  
	  if (j != UNDEF) {

	    if (m[j][j] + 2*m[i][j] != 0) {

	      FF_ASSERT(PROPAGATOR, m[i][j] != 0);
	      for (int s = 0; s < n; ++s) {
		// (a[i][s], a[j][s]) := (a[i][s] + a[j][s], a[i][s] - a[j][s])
		// a[k][s] does not change if k != i, j.
		Zp aux = a[j][s];
		neg_assign(a[j][s]);
		a[j][s] += a[i][s];
		a[i][s] += aux;
	      }

	      // (v[i], v[j]) := ((v[i] + v[j])/2, (v[i] - v[j])/2)
	      // v[k] does not change if k != i, j.
	      Zp aux = v[j];
	      neg_assign(v[j]);
	      v[j] += v[i];
	      v[j] = v[j] / 2;
	      v[i] += aux;
	      v[i] = v[i] / 2;

	      // (m[i][s], m[j][s]) := ( (m[i][s] + m[j][s])/2, (m[i][s] - m[j][s])/2) for s != i, j
	      // (m[i][i], m[i][j], m[j][j]) := ((m[j][j] + 2 m[i][j])/4, -m[j][j]/4, (m[j][j] - 2 m[i][j])/4)
	      for (int s = 0; s < i; ++s) {
		Zp aux = m[s][j];
		neg_assign(m[s][j]);
		m[s][j] += m[s][i];
		m[s][j] = m[s][j] / 2;
		m[s][i] += aux;
		m[s][i] = m[s][i] / 2;
	      }
	      for (int s = i+1; s < j; ++s) {
		Zp aux = m[s][j];
		neg_assign(m[s][j]);
		m[s][j] += m[i][s];
		m[s][j] = m[s][j] / 2;
		m[i][s] += aux;
		m[i][s] = m[i][s] / 2;
	      }

	      for (int s = j+1; s < n; ++s) {
		Zp aux = m[j][s];
		neg_assign(m[j][s]);
		m[j][s] += m[i][s];
		m[j][s] = m[j][s] / 2;
		m[i][s] += aux;
		m[i][s] = m[i][s] / 2;
	      }

	      aux = m[i][j];
	      m[i][j] = -m[j][j] / 4;
	      m[i][i] = (m[j][j] + 2*aux) / 4;
	      m[j][j] = (m[j][j] - 2*aux) / 4;
	    }
	    else {
	      FF_ASSERT(PROPAGATOR, m[i][j] != 0);
	      for (int s = 0; s < n; ++s) {
		// (a[i][s], a[j][s]) := (a[j][s] - a[i][s], a[i][s] + a[j][s])
		// a[k][s] does not change if k != i, j.
		Zp aux = a[i][s];
		neg_assign(a[i][s]);
		a[i][s] += a[j][s];
		a[j][s] += aux;
	      }

	      // (v[i], v[j]) := ((v[j] - v[i])/2, (v[i] + v[j])/2)
	      // v[k] does not change if k != i, j.
	      Zp aux = v[i];
	      neg_assign(v[i]);
	      v[i] += v[j];
	      v[i] = v[i] / 2;
	      v[j] += aux;
	      v[j] = v[j] / 2;

	      // (m[i][s], m[j][s]) := ( (m[j][s] - m[i][s])/2, (m[i][s] + m[j][s])/2) for s != i, j
	      // (m[i][i], m[i][j], m[j][j]) := ((m[j][j] - 2 m[i][j])/4, m[j][j]/4, (m[j][j] + 2 m[i][j])/4)
	      
	      for (int s = 0; s < i; ++s) {
		Zp aux = m[s][i];
		neg_assign(m[s][i]);
		m[s][i] += m[s][j];
		m[s][i] = m[s][i] / 2;
		m[s][j] += aux;
		m[s][j] = m[s][j] / 2;
	      }
	      for (int s = i+1; s < j; ++s) {
		Zp aux = m[s][i];
		neg_assign(m[s][i]);
		m[s][i] += m[j][s];
		m[s][i] = m[s][i] / 2;
		m[j][s] += aux;
		m[j][s] = m[j][s] / 2;
	      }

	      for (int s = j+1; s < n; ++s) {
		Zp aux = m[i][s];
		neg_assign(m[i][s]);
		m[i][s] += m[j][s];
		m[i][s] = m[i][s] / 2;
		m[j][s] += aux;
		m[j][s] = m[j][s] / 2;
	      }

	      aux = m[i][j];
	      m[i][j] =  m[j][j] / 4;
	      m[i][i] = (m[j][j] - 2*aux) / 4;
	      m[j][j] = (m[j][j] + 2*aux) / 4;
	    }
	    FF_ASSERT(PROPAGATOR, m[i][i] != 0);
	  }
	  else ++i;
	}
	else {

	  for (int j = 0; j < n; ++j) {
	    if (i != j) {
	      Zp aux = (i < j ? m[i][j] : m[j][i]);
	      aux = aux / m[i][i];
	      v[j] = v[j] - aux * v[i];
	      for (int s = 0; s < n; ++s)
		a[i][s] += aux * a[j][s];
	    }
	  }

	  for (int r = 0; r < n; ++r) {
	    for (int s = r; s < n; ++s) {
	      if (r != i and s != i) {
		Zp aux_r = (i < r ? m[i][r] : m[r][i]);
		Zp aux_s = (i < s ? m[i][s] : m[s][i]);
		m[r][s] = m[r][s] - aux_r * aux_s / m[i][i];
	      }
	    }
	  }
	  for (int r =   0; r < i; ++r) m[r][i] = 0;
	  for (int r = i+1; r < n; ++r) m[i][r] = 0;

	  ++i;
	}
      }


      // 2. Eliminate linear terms.

      for (int i = 0; i < n; ++i) {
	if (m[i][i] != 0 and v[i] != 0) {
	  k = k - v[i] * v[i] / (4 * m[i][i]);
	  b[i] += v[i] / (2 * m[i][i]);
	  v[i] = 0;
	}
      }

      const int UNDEF = -1;
      int quad1 = UNDEF;
      int quad2 = UNDEF;

      int ok = true;
      for (int i = 0; i < n; ++i) {
	if (m[i][i] != 0) {
	  if      (quad1 == UNDEF) quad1 = i;
	  else if (quad2 == UNDEF) quad2 = i;
	  else {
	    ok = false;
	    break;
	  }
	}
      }
      if (ok) {
	if (quad1 == UNDEF) {
	  // Polynomial is already linear
	  return;
	}
	else if (quad2 == UNDEF) {

	  int i = quad1;

	  // Normalize.
	  for (int j = 0; j < n; ++j) {
	    v[j] = v[j] / m[i][i];
	  }
	  k = k / m[i][i];
	  m[i][i] = 1;

	  bool empty_linear_part = true;
	  for (int i = 0; i < n; ++i) {
	    if (v[i] != 0) {
	      empty_linear_part = false;
	      break;
	    }
	  }

	  Polynomial<Zp> r;
	  if (b[i] != 0)
	    r = Polynomial<Zp>(b[i], Monomial());
	  for (int j = 0; j < n; ++j) {
	    if (a[i][j] != 0)
	      r = r + Polynomial<Zp>(a[i][j], Monomial(intn2extn[j]));
	  }

	  if (empty_linear_part) {

	    if (k == 0) {
	      res.push_back( { {r, true} } );
	    }
	    else if (rooter.is_square(-k)) {
	      Zp sq = rooter.square_root(-k);
	      Polynomial<Zp> r1 = r + Polynomial<Zp>(-sq);
	      Polynomial<Zp> r2 = r + Polynomial<Zp>( sq);
	      res.push_back( { {r1, true}, {r2, true} } );
	    }
	    else {
	      res.push_back( { {Polynomial<Zp>(1, Monomial()), true} } );
	    }
	  }
	  else {

	    Polynomial<Zp> s;
	    if (k != 0) s = Polynomial<Zp>(k, Monomial());

	    for (int i = 0; i < n; ++i) {
	      if (v[i] != 0) {
		Polynomial<Zp> t;
		if (b[i] != 0)
		  t = Polynomial<Zp>(b[i], Monomial());
		for (int j = 0; j < n; ++j) {
		  if (a[i][j] != 0)
		    t = t + Polynomial<Zp>(a[i][j], Monomial(intn2extn[j]));
		}
		s = s + Polynomial<Zp>(v[i]) * t;
	      }
	    }
	    res.push_back( { {s, false}, {r, true},  } );
	    res.push_back( { {r, false}, {s, true},  } );
	  }
	}
	else {

	  int i = quad1;
	  int j = quad2;

	  // Normalize.
	  for (int t = 0; t < n; ++t) {
	    v[t] = v[t] / m[i][i];
	  }
	  k = k / m[i][i];
	  m[j][j] = m[j][j] / m[i][i];
	  m[i][i] = 1;

	  bool empty_linear_part = true;
	  for (int i = 0; i < n; ++i) {
	    if (v[i] != 0) {
	      empty_linear_part = false;
	      break;
	    }
	  }

	  Polynomial<Zp> ri;
	  if (b[i] != 0)
	    ri = Polynomial<Zp>(b[i], Monomial());
	  for (int t = 0; t < n; ++t) {
	    if (a[i][t] != 0)
	      ri = ri + Polynomial<Zp>(a[i][t], Monomial(intn2extn[t]));
	  }

	  Polynomial<Zp> rj;
	  if (b[j] != 0)
	    rj = Polynomial<Zp>(b[j], Monomial());
	  for (int t = 0; t < n; ++t) {
	    if (a[j][t] != 0)
	      rj = rj + Polynomial<Zp>(a[j][t], Monomial(intn2extn[t]));
	  }

	  if (empty_linear_part) {
	    if (k == 0) {

	      if (rooter.is_square(-m[j][j])) {
		Zp sq = rooter.square_root(-m[j][j]);
		res.push_back( { {ri + Polynomial<Zp>( sq) * rj, true},
				 {ri + Polynomial<Zp>(-sq) * rj, true} } );
	      }
	      else {
		res.push_back( { {ri, true} } );
		res.push_back( { {rj, true} } );
	      }
	    }
	    else {
	      if (rooter.is_square(-m[j][j])) {
		Zp sq = rooter.square_root(-m[j][j]);
		res.push_back( { {ri + Polynomial<Zp>( sq) * rj, false} } );
		res.push_back( { {ri + Polynomial<Zp>(-sq) * rj, false} } );
	      }
	      else return;
	    }
	  }
	  else {

	    if (rooter.is_square(-m[j][j])) {
	      Zp sq = rooter.square_root(-m[j][j]);
	      Polynomial<Zp> s;
	      if (k != 0) s = Polynomial<Zp>(k, Monomial());

	      for (int i = 0; i < n; ++i) {
		if (v[i] != 0) {
		  Polynomial<Zp> t;
		  if (b[i] != 0)
		    t = Polynomial<Zp>(b[i], Monomial());
		  for (int j = 0; j < n; ++j) {
		    if (a[i][j] != 0)
		      t = t + Polynomial<Zp>(a[i][j], Monomial(intn2extn[j]));
		  }
		  s = s + Polynomial<Zp>(v[i]) * t;
		}
	      }

	      res.push_back( { {s, false},
			       {ri + Polynomial<Zp>( sq) * rj, true},
			       {ri + Polynomial<Zp>(-sq) * rj, true} } );

	      res.push_back( { {ri + Polynomial<Zp>( sq) * rj, false}, {s, true} } );
	      res.push_back( { {ri + Polynomial<Zp>(-sq) * rj, false}, {s, true} } );
	    }
	    else return;
	  }
	}
      }
      else return;
    }
  }


  vector< vector< pair<Polynomial<Zp>, bool> > >  result() {

    for (auto& v : res) {
      for (auto& [q, e] : v) {
	q.normalize();
      }
    }

    return res;
  }


  friend ostream& operator << (ostream& out, const Propagator& prop) {

    const auto& [_, ok, m, v, k, extn2intn, intn2extn, a, b, res] = prop;

    if (not ok) {
      out << "Invalid" << endl;
      return out;
    }

    int n = m.size();

    // Degree 2.
    out << endl;
    out << "\t";
    for (int j = 0; j < n; ++j) {
      out << Context::Variable(intn2extn[j]) << "\t";
    }
    out << endl;
    for (int i = 0; i < n; ++i) {
      out << Context::Variable(intn2extn[i]) << "\t";
      for (int j = 0; j < n; ++j) {
	out << (i < j ? m[i][j] : m[j][i]) << "\t";
      }
      out << endl;
    }

    // Degree 1.
    out << endl;
    for (int i = 0; i < n; ++i)
      out << Context::Variable(intn2extn[i]) << "\t" << v[i] << endl;

    // Degree 0.
    out << endl;
    out << k << endl;

    out << endl;
    for (int i = 0; i < n; ++i) {
      for (int j = 0; j < n; ++j) {
	out << a[i][j] << "\t";
      }
      out << endl;
    }

    out << endl;
    for (int i = 0; i < n; ++i)
      out << b[i] << endl;

    return out;
  }


private:

  int variable(int extn) {
    int intn = intn2extn.size();
    const auto& [it, added] = extn2intn.insert({extn, intn});
    if (added) {
      intn2extn.push_back(extn);
      v.push_back(0);
      int n = m.size();
      for (int i = 0; i < n; ++i) {
	m[i].push_back(0);
      }
      m.push_back(vector<Zp>(n+1, 0));
    }
    return it->second;
  }

  const Square_rooter& rooter;

  bool               ok; // Polynomial has degree <= 2.
  vector<vector<Zp>> m;  // Matrix of quadratic terms.
  vector<Zp>         v;  // Vector of linear terms.
  Zp                 k;  // Scalar of constant term.

  // Map external variables <--> internal variables.
  map<int,int>       extn2intn;
  vector<int>        intn2extn;

  // Let y = new (internal) variables
  //     x = old (internal) variables
  // Then y = a x + b
  vector<vector<Zp>> a;
  vector<Zp>         b;

  vector< vector< pair<Polynomial<Zp>, bool> > > res;
};

} // namespace FF

#endif // PROPAGATOR_HH

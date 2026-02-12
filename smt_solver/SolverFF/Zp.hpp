#ifndef FF_ZP_HPP
#define FF_ZP_HPP

#include "Global.hpp"

extern string prime;

namespace FF {


class Zp {

  mpz_class v;

  // Only to be used if a divides exactly as an integer.
  Zp& operator/=(const Zp& a) {
    v /= a.v;
    return *this;
  }

  // Only this class is allowed to call operator/=(const Zp& a)
  // since divisions are exact as required.
  friend class F_matrix;
  friend class C_matrix;

  
public:

  static mpz_class p;
  static mpz_class h;
  
  static void assign_modulo(const mpz_class& n, mpz_class& m) {
    m = n % p;
    if      (m >  h) m -= p;
    else if (m < -h) m += p;
  }


  Zp(int n = 0) {
    assign_modulo(n, v);
    FF_ASSERT(ZP, -h <= v and v <= h);
  }


  Zp(const mpz_class& n) {
    assign_modulo(n, v);
    FF_ASSERT(ZP, -h <= v and v <= h);
  }
  

  Zp(string str) {
    assign_modulo(mpz_class(str), v);
    FF_ASSERT(ZP, -h <= v and v <= h);
  }


  const mpz_class& get_v() const {
    FF_ASSERT(ZP, -h <= v and v <= h);

    // previous version of bounds analysis uses [0,p], changing to that for the analysis
    

    return v;
  }


  friend ostream& operator << (ostream& out, const Zp& a) {

    FF_ASSERT(ZP, -h <= a.v and a.v <= h);

    // Representative in [-(p-1)/2, (p-1)/2]
    if   (a.v >= 0) out <<        a.v;
    else            out << '(' << a.v << ')';

    return out;
  }


  Zp& operator+=(const Zp& a) {
    FF_ASSERT(ZP, -h <= a.v and a.v <= h);
    v += a.v;
    if      (v >  h) v -= p;
    else if (v < -h) v += p;
    FF_ASSERT(ZP, -h <= v and v <= h);
    return *this;
  }


  Zp& operator*=(const Zp& a) {
    FF_ASSERT(ZP, -h <= a.v and a.v <= h);
    v *= a.v;
    Zp::assign_modulo(v, v);
    FF_ASSERT(ZP, -h <= v and v <= h);
    return *this;
  }
  

  friend Zp operator -(const Zp& a);
  friend Zp operator +(const Zp& a, const Zp& b);
  friend Zp operator -(const Zp& a, const Zp& b);
  friend Zp operator *(const Zp& a, const Zp& b);
  friend Zp operator /(const Zp& a, const Zp& b);

  friend bool operator ==(const Zp& a, const Zp& b);
  friend bool operator !=(const Zp& a, const Zp& b);
  friend bool operator  <(const Zp& a, const Zp& b); // For defining maps!
  
  friend bool is_positive(const Zp& a);
  friend bool is_negative(const Zp& a);

  friend void neg_assign(Zp& a);
  friend void neg_assign(Zp& a, const Zp& b);
  friend void gcd_assign(Zp& a, const Zp& b, const Zp& c);
  
};


inline Zp operator -(const Zp& a) {
#if FF_DEBUG
  const mpz_class& h = Zp::h;
#endif  
  FF_ASSERT(ZP, -h <= a.v and a.v <= h);
  if (a.v == 0) return a;
  Zp c;
  c.v = - a.v;
  FF_ASSERT(ZP, a + c == Zp(0));
  FF_ASSERT(ZP, -h <= c.v and c.v <= h);
  return c;
}


inline Zp operator +(const Zp& a, const Zp& b) {
  const mpz_class& p = Zp::p;
  const mpz_class& h = Zp::h;  
  FF_ASSERT(ZP, -h <= a.v and a.v <= h);
  FF_ASSERT(ZP, -h <= b.v and b.v <= h);
  Zp c;
  c.v = a.v + b.v;
  if      (c.v >  h) c.v -= p;
  else if (c.v < -h) c.v += p;
  FF_ASSERT(ZP, -h <= c.v and c.v <= h);
  return c;
}


inline Zp operator -(const Zp& a, const Zp& b) {
  const mpz_class& p = Zp::p;
  const mpz_class& h = Zp::h;  
  FF_ASSERT(ZP, -h <= a.v and a.v <= h);
  FF_ASSERT(ZP, -h <= b.v and b.v <= h);
  Zp c;
  c.v = a.v - b.v;
  if      (c.v >  h) c.v -= p;
  else if (c.v < -h) c.v += p;
  FF_ASSERT(ZP, -h <= c.v and c.v <= h);
  return c;
}
  

inline Zp operator *(const Zp& a, const Zp& b) {
#if FF_DEBUG
  const mpz_class& h = Zp::h;
#endif  
  FF_ASSERT(ZP, -h <= a.v and a.v <= h);
  FF_ASSERT(ZP, -h <= b.v and b.v <= h);
  Zp c;
  c.v = a.v * b.v;
  Zp::assign_modulo(c.v, c.v);
  FF_ASSERT(ZP, -h <= c.v and c.v <= h);
  return c;
}


inline Zp operator /(const Zp& a, const Zp& b) {
  const mpz_class& p = Zp::p;
#if FF_DEBUG
  const mpz_class& h = Zp::h;
#endif  
  FF_ASSERT(ZP, -h <= a.v and a.v <= h);
  FF_ASSERT(ZP, -h <= b.v and b.v <= h);
  Zp c;
  mpz_class g, t;
  mpz_gcdext(g.get_mpz_t(), c.v.get_mpz_t(), t.get_mpz_t(), b.v.get_mpz_t(), p.get_mpz_t());
  FF_ASSERT(ZP, g == 1);
  Zp::assign_modulo(c.v, c.v);
  c *= a;
  FF_ASSERT(ZP, b * c == a);
  FF_ASSERT(ZP, -h <= c.v and c.v <= h);
  return c;
}


inline bool operator ==(const Zp& a, const Zp& b) {
  return a.v == b.v;
}


inline bool operator !=(const Zp& a, const Zp& b) {
  return not(a == b);
}


inline bool is_zero(const Zp& a) { return a == Zp(0); }
inline bool is_one (const Zp& a) { return a == Zp(1); }

inline bool is_positive (const Zp& a) {
  return a.v >= 0; 
}

inline bool is_negative (const Zp& a) {
  return a.v < 0; 
}



inline bool operator <(const Zp& a, const Zp& b) {
  return a.v < b.v;
}


inline void neg_assign(Zp& a) {
  a = -a;
}


inline void neg_assign(Zp& a, const Zp& b) {
  a = -b;
}


inline void gcd_assign(Zp& a, const Zp& b, const Zp& c) {
  mpz_gcd(a.v.get_mpz_t(), b.v.get_mpz_t(), c.v.get_mpz_t());
}


inline Zp pow(const Zp& a, int n) {
  Zp x(a);
  Zp y(1);
  while (n != 0) {
    // n even: y * x^n = y * (x^2)^(n/2)
    // n  odd: y * x^n = y * x * x^(n-1)
    if (n % 2 == 0) {
      Zp z = x;
      x *= x;
      n /= 2;
    }
    else {
      y *= x;
      --n;
    }
  }
  return y;
}


////////////////////////////////////////////////////////////////
  
} // namespace FF
  
#endif // FF_ZP_HPP

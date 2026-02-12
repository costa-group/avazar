#ifndef SQUARE_ROOTER_HH
#define SQUARE_ROOTER_HH

#include "Zp.hpp"

namespace FF {

inline bool is_even(const mpz_class& n) {
    // Test whether the least significant bit is 0
    return mpz_tstbit(n.get_mpz_t(), 0) == 0;
}


inline Zp power(const Zp& a, const mpz_class& b) {
  auto x = a;
  auto y = b;
  auto z = Zp(1);
  while (y != 0) {
    if (y % 2 == 1) z *= x;
    x *= x;
    y /= 2;
  }
  return z;
}


inline Zp legendre_symbol(const Zp& a) {
  const auto& p = Zp::p;
  return power(a, (p-1)/2);
}


class Square_rooter {

  // See https://en.wikipedia.org/wiki/Tonelli%E2%80%93Shanks_algorithm

public:

  Square_rooter() {
    const auto& p = Zp::p;
    prime_is_3_mod_4 = (Zp::p % 4 == 3);
    prime_is_5_mod_8 = (Zp::p % 8 == 5);
    if (not prime_is_3_mod_4 and not prime_is_5_mod_8) {
      z = 2;
      while (is_square(z)) {
	z += 1;
	if      (z == Zp( 4)) z += 1;
	else if (z == Zp( 9)) z += 1;
	else if (z == Zp(25)) z += 1;
      }
      Q = p - 1;
      S = 0;
      while (is_even(Q)) {
	Q >>= 1;
	++S;
      }
    }
  }


  bool is_square(const Zp& n) const {
    if (n == Zp(0)) return true;
    if (n == Zp(1)) return true;
    if (n == Zp(4)) return true;
    if (n == Zp(9)) return true;
    return legendre_symbol(n) != Zp(-1);
  }


  Zp square_root(const Zp& n) const {

    const auto& p = Zp::p;

    if (n == Zp(0)) return Zp(0);
    if (n == Zp(1)) return Zp(1);
    if (n == Zp(4)) return Zp(2);
    if (n == Zp(9)) return Zp(3);

    if (prime_is_3_mod_4) {
      return power(n, (p+1)/4);
    }

    if (prime_is_5_mod_8) {
      if (power(n, (p-1)/4) == Zp(1))
	return power(n, (p+3)/8);
      else
	return 2 * n * power(4*n, (p-5)/8);
    }

    mpz_class M = S;
    Zp c = power(z, Q);
    Zp t = power(n, Q);
    Zp R = power(n, (Q+1)/2);

    FF_ASSERT(PROPAGATOR, n != Zp(0));
    while (t != Zp(1)) {
      Zp u = t * t;
      mpz_class i = 1;
      while (u != Zp(1)) {
	u = u * u;
	++i;
      }

      Zp b = c;
      for (mpz_class j = 0; j < M - i - 1; ++j) b = b * b;

      M = i;
      c = b * b;
      t = t * c;
      R = R * b;
    }
    FF_ASSERT(PROPAGATOR, R*R == n);
    return R;
  }


private:

  Zp z;
  bool prime_is_3_mod_4;
  bool prime_is_5_mod_8;

  mpz_class Q, S;

};

////////////////////////////////////////////////////////////////

} // namespace FF

#endif // SQUARE_ROOTER_HH

#ifndef FF_MONOMIAL_HPP
#define FF_MONOMIAL_HPP

#include "Global.hpp"
#include "Context.hpp"

namespace FF {

class Monomial {

public:
  
  vector<pair<int, int>> w; // Pairs of {variable, exponent}.

  using Const_Iterator = vector<pair<int, int>>::const_iterator;

  friend ostream& operator << (ostream& out, const Monomial& mon);


  bool ok() const { return is_sorted(w.begin(), w.end()); }
  
  Const_Iterator  begin() const { return w.cbegin(); }
  Const_Iterator    end() const { return w.  cend(); }
  
  std::size_t size() const { return w.size(); }

  Monomial( ) { }


  Monomial(int u, int e = 1) {
    // Monomials can only be constructed with original finite field variables.
    FF_ASSERT(MONOMIAL, u >= 0); 
    w.push_back({u, e});
  }


  void normalize() {
    sort(w.begin(), w.end());
  }


  friend bool is_nonlinear(const Monomial& a) {
    const auto& w = a.w;
    if (w.empty())    return false;
    if (w.size() > 1) return true;
    FF_ASSERT(MONOMIAL, w.size() == 1);
    return w.front().second > 1;
  }

  // Returns the monomial without the variable and the degree of the var
  friend pair<Monomial, int> perform_assignment(const Monomial& a, int signal){
    Monomial r;
    int exp = 0;

    int a_size = a.w.size();


    for (int i = 0; i < a_size; i++) {
      const auto& [av, ae] = a.w[i];
      if (av == signal){
        exp = ae;
      } else{
        r.w.push_back({av, ae});
      }
    }
    return {r, exp};
  }

  // Applies the substitution signal_eliminated -> signal_new
  friend Monomial perform_assignment_to_signal(const Monomial& a, int signal_eliminated, int signal_new) {
    Monomial r;

    int index_signal_new = -1;
    int a_size = a.w.size();


    for (int i = 0; i < a_size; i++) {
      const auto& [av, ae] = a.w[i];
      if (av == signal_eliminated || av == signal_new){
        if (index_signal_new != -1){
          // in case we have already found the new signal
          auto [should_be_signal_new, previous_e] = r.w[index_signal_new];
          assert(should_be_signal_new == signal_new);
          r.w[index_signal_new] = {signal_new, previous_e + ae};
        } else{
          // in case we have not found the new signal yet
          index_signal_new = r.w.size();
          r.w.push_back({signal_new, ae});
        }
      } else{
        r.w.push_back({av, ae});
      }
    }
    r.normalize();
    return r;
  }


  friend bool contains_signal(const Monomial& a, int signal){
  
    int a_size = a.w.size();
  
    for (int i = 0; i < a_size; i++) {
      const auto& [av, ae] = a.w[i];
      if (av == signal){
        return true;
      } 
    }
    return false;
  }

  friend set<int> get_signals(const Monomial & a){
    set<int> signals;
    int a_size = a.w.size();

    for (int i = 0; i < a_size; i++) {
      const auto& [av, ae] = a.w[i];
      signals.insert(av);
    }
    return signals;
  }

  
  friend bool is_one(const Monomial& a) {
    return a.w.empty();
  }

  friend bool is_single_signal(const Monomial& a) {
    return (a.w.size() == 1) && (a.w[0].second == 1);
  }

  friend bool is_quadratic_signal(const Monomial& a) {
    return (a.w.size() == 1) && (a.w[0].second == 2);
  }
  

  friend Monomial operator *(const Monomial& a,
                             const Monomial& b) {

    FF_ASSERT(MONOMIAL, a.ok());
    FF_ASSERT(MONOMIAL, b.ok());

    Monomial r;

    int a_size = a.w.size();
    int b_size = b.w.size();
    
    int i = 0, j = 0;
    while (i < a_size and j < b_size) {
      const auto& [av, ae] = a.w[i];
      const auto& [bv, be] = b.w[j];
      if      (av < bv) { r.w.push_back({av, ae     }); ++i;      }
      else if (av > bv) { r.w.push_back({bv, be     });      ++j; }
      else              { r.w.push_back({av, ae + be}); ++i; ++j; }
    }
    while (i < a_size)  { r.w.push_back(a.w[i]); ++i; }
    while (j < b_size)  { r.w.push_back(b.w[j]); ++j; }
    return r;
  }
      
  
  friend bool operator < (const Monomial& a,
                          const Monomial& b) {

    FF_ASSERT(MONOMIAL, a.ok());
    FF_ASSERT(MONOMIAL, b.ok());
    
    int a_size = a.w.size();
    int b_size = b.w.size();

    int k = 0;
    while (k < a_size and k < b_size) {
      const auto& [av, ae] = a.w[k];
      const auto& [bv, be] = b.w[k];
      if      (av < bv) return false;
      else if (av > bv) return true;
      else if (ae < be) return true;
      else if (ae > be) return false;
      else ++k;
    }
    return k < b_size;
  }


  friend bool operator > (const Monomial& a,
                          const Monomial& b) {
    FF_ASSERT(MONOMIAL, a.ok());
    FF_ASSERT(MONOMIAL, b.ok());
    return b < a;
  }

  friend bool operator <= (const Monomial& a,
                           const Monomial& b) {
    FF_ASSERT(MONOMIAL, a.ok());
    FF_ASSERT(MONOMIAL, b.ok());
    return not(b < a);
  }


  friend bool operator >= (const Monomial& a,
                           const Monomial& b) {
    FF_ASSERT(MONOMIAL, a.ok());
    FF_ASSERT(MONOMIAL, b.ok());
    return not(a < b);
  }


  friend bool operator == (const Monomial& a,
                           const Monomial& b) {
    FF_ASSERT(MONOMIAL, a.ok());
    FF_ASSERT(MONOMIAL, b.ok());
    return a.w == b.w;
  }


  friend bool operator != (const Monomial& a,
                           const Monomial& b) {
    FF_ASSERT(MONOMIAL, a.ok());
    FF_ASSERT(MONOMIAL, b.ok());
    return not(a == b);
  }

  template <typename Coefficient_Type>
  Coefficient_Type evaluate(const vector<Coefficient_Type>& var2val) {
    Coefficient_Type res = Coefficient_Type(1);
    for (const auto& [var, exp] : w) 
      res *= pow(var2val[var], exp);
    return res;
  }

};


inline ostream& operator << (ostream& out, const Monomial& mon) {

  string sep = (pretty_printing_on ? " " : " * ");
  if (mon.w.empty()) {
    out << "1";
  }
  else {
    bool first = true;
    for (const auto& [var, exp] : mon.w) {
      if (first) first = false;
      else       out << sep;
      FF_ASSERT(MONOMIAL, exp > 0);
      FF_ASSERT(MONOMIAL, var >= 0);
      out << Context::Variable(var);
      if (exp > 1) out << "^" << exp;
    }
  }
  return out;
}


} // namespace FF
  
#endif // FF_MONOMIAL_HPP

#ifndef FF_POLYNOMIAL_HPP
#define FF_POLYNOMIAL_HPP

#include "Monomial.hpp"

namespace FF {

template <typename Coefficient_Type>
class Polynomial {

public:
  
  map<Monomial, Coefficient_Type> mon2coeff;

  bool known_roots;
  vector<pair<int, Coefficient_Type>> roots;
  using Const_Iterator = typename map<Monomial, Coefficient_Type>::const_iterator;


  bool ok() const {
    for (const auto& [mon, _] : mon2coeff)
      if (not mon.ok())
	return false;
    return true;
  }

  
  Const_Iterator  begin() const { return mon2coeff.cbegin(); }
  Const_Iterator    end() const { return mon2coeff.  cend(); }
  
  Polynomial() : mon2coeff(), roots() { 
    known_roots = true;
  }
  
  Polynomial(const Coefficient_Type& c, const Monomial& m) {
    mon2coeff.insert({m, c});
    known_roots = true;
    set<int> signals = get_signals(m);
    for (int s: signals){
      roots.push_back({s, 0});
    }
  }

  explicit Polynomial(const Coefficient_Type& c) {
    mon2coeff.insert({ Monomial(), c});
    known_roots = true;
  }
  
  // Returns the constant term in a polynomial.
  Coefficient_Type constant() const {
    if (mon2coeff.empty()) return Coefficient_Type(0);
    else {
      const auto& [mon, coe] = *(mon2coeff.begin());
      if (is_one(mon)) return coe;
      else             return Coefficient_Type(0);
    }
  }

  // Returns the polynomial without the constant term.
  Polynomial<Coefficient_Type> non_constant() const {
    Polynomial<Coefficient_Type> res = *this;
    res.mon2coeff.erase(Monomial());
    return res;
  }


  void normalize() {
    FF_ASSERT(POLYNOMIAL, not mon2coeff.empty());

    if (mon2coeff.size() == 1 or (mon2coeff.size() == 2 and is_one(mon2coeff.begin()->first))) {
      auto [_, lead] = *mon2coeff.rbegin();
      for (auto& [mon, coeff] : mon2coeff) 
	coeff = coeff / lead;
      return;
    }
    
    // For normalizing, choose the coefficient by taking the one that minimizes
    // the maximum absolute value of the representatives of the resulting coefficients.
    
    bool      min_norm_def   = false;
    mpz_class min_norm_cost;
    Zp        min_norm_coeff = 0;
    for (const auto& [_, norm_coeff] : mon2coeff) {
      mpz_class norm_cost = 0;
      for (const auto& [_, coeff] : mon2coeff) {
	Zp aux = coeff / norm_coeff;
	mpz_class cost = aux.get_v();
	if (cost < 0) cost = -cost;
	if (norm_cost < cost) norm_cost = cost;
      }
      
      if (not min_norm_def or min_norm_cost > norm_cost) {
	min_norm_def   = true;
	min_norm_cost  = norm_cost;
	min_norm_coeff = norm_coeff;
      } 
    }

    FF_ASSERT(POLYNOMIAL, min_norm_def);
    FF_ASSERT(POLYNOMIAL, min_norm_coeff != 0);
    for (auto& [_, coeff] : mon2coeff) 
      coeff = coeff / min_norm_coeff;
  }
  

  bool is_normalized() const {
    auto copy = *this;
    copy.normalize();
    return *this == copy;
  }
  
  int size() const{
      return mon2coeff.size();
  }
  
  template <typename Coeff_Type>
  friend bool
  is_zero(const Polynomial<Coeff_Type>& p);


  template <typename Coeff_Type>
  friend bool
  is_nonzero_constant(const Polynomial<Coeff_Type>& p);

  template <typename Coeff_Type>
  friend bool
  is_one(const Polynomial<Coeff_Type>& p);

  template <typename Coeff_Type>
  friend bool
  is_minus_one(const Polynomial<Coeff_Type>& p);

  template <typename Coeff_Type>
  friend bool
  is_single_signal(const Polynomial<Coeff_Type>& p);
  

  template <typename Coeff_Type>
  friend Polynomial<Coeff_Type>
  operator +(const Polynomial<Coeff_Type>& p,
	     const Polynomial<Coeff_Type>& q);


  template <typename Coeff_Type>
  friend Polynomial<Coeff_Type>
  operator *(const Coeff_Type& a,
	     const Polynomial<Coeff_Type>& p);


  template <typename Coeff_Type>
  friend Polynomial<Coeff_Type>
  operator *(const Monomial& a,
	     const Polynomial<Coeff_Type>& p);  
  

  friend ostream& operator << (ostream& out,
			       const Polynomial<Coefficient_Type>& p) {

    const map<Monomial, Coefficient_Type>& c = p.mon2coeff;

    string sep = (pretty_printing_on ? " " : " * ");

    if (c.empty()) out << "0";
    else {
      auto j = c.begin();
      auto e = c.end();
      --e;
      while (j != e) {
	if      (is_one(j->second)) out                      << j->first << " + ";
	else if (is_one(j->first )) out <<  j->second                    << " + ";
	else                        out <<  j->second << sep << j->first << " + ";
	++j;
      }
      if      (is_one(e->second))   out                      << e->first;
      else if (is_one(e->first ))   out << e->second;
      else                          out << e->second  << sep << e->first;
    }
    return out;
  }


  // Needed for maps with polynomial keys.
  template <typename Coeff_Type>
  friend bool
  operator <(const Polynomial<Coeff_Type>& p,
	     const Polynomial<Coeff_Type>& q) {
    return p.mon2coeff < q.mon2coeff;
  }


  template <typename Coeff_Type>
  friend bool
  operator ==(const Polynomial<Coeff_Type>& p,
	      const Polynomial<Coeff_Type>& q) {
    return p.mon2coeff == q.mon2coeff;
  }


  template <typename Coeff_Type>
  friend bool
  operator !=(const Polynomial<Coeff_Type>& p,
	      const Polynomial<Coeff_Type>& q) {
    return not(p.mon2coeff == q.mon2coeff);
  }
  

  template <typename Coeff_Type>
  friend Polynomial<Coeff_Type>
  operator *(const Polynomial<Coeff_Type>& a,
	     const Polynomial<Coeff_Type>& b);

  Coefficient_Type evaluate(const vector<Coefficient_Type>& var2val) {
    Coefficient_Type res = Coefficient_Type(0);
    for (const auto& [mon, coeff] : mon2coeff)
      res += coeff * mon.evaluate(var2val);
    return res;
  }

};


template <typename Coeff_Type>
bool
is_zero(const Polynomial<Coeff_Type>& p) {
  return p.mon2coeff.empty();
}


template <typename Coeff_Type>
bool
is_nonzero_constant(const Polynomial<Coeff_Type>& p) {
  if (p.mon2coeff.size() != 1) return false;
  const auto& [mon, coeff] = *p.mon2coeff.begin();
  FF_ASSERT(POLYNOMIAL, not is_zero(coeff));
  return is_one(mon);
}

template <typename Coeff_Type>
bool
is_one(const Polynomial<Coeff_Type>& p) {
  if (p.mon2coeff.size() != 1) return false;
  const auto& [mon, coeff] = *p.mon2coeff.begin();
  FF_ASSERT(POLYNOMIAL, not is_zero(coeff));
  return is_one(mon) && coeff == 1;
}

template <typename Coeff_Type>
bool
is_minus_one(const Polynomial<Coeff_Type>& p) {
  if (p.mon2coeff.size() != 1) return false;
  const auto& [mon, coeff] = *p.mon2coeff.begin();
  FF_ASSERT(POLYNOMIAL, not is_zero(coeff));
  return is_one(mon) && -coeff == 1;
}

template <typename Coeff_Type>
bool 
is_single_signal(const Polynomial<Coeff_Type>& p) {
  if (p.mon2coeff.size() != 1) return false;
  const auto& [mon, coeff] = *p.mon2coeff.begin();
  FF_ASSERT(POLYNOMIAL, not is_zero(coeff));
  return mon == 1 && is_single_signal(mon);
}

template <typename Coeff_Type>
bool is_linear(const Polynomial<Coeff_Type> & p) {
  auto i = p.begin();
  while (i != p.end()) {
    if (is_nonlinear(i->first)){
      return false;
    }
    i++;
  }
  return true;
}

template <typename Coeff_Type>
tuple<bool, int, Coeff_Type> is_signal_eq_constant(const Polynomial<Coeff_Type> & p){
  // A * x + B ==> returns (x, -B / A)
  tuple<bool, int, Coeff_Type> result = {false, 0, 0};
  if (p.mon2coeff.size() == 1){
    if (is_single_signal(p)){
      auto [mon, coef] = *p.mon2coeff.begin();
      int signal = mon.w[0].first;
      result =  {true, signal, 0};
    }
  } else if (p.mon2coeff.size() == 2){
    bool found_x = false;
    int x;
    Zp coef_x;
    bool found_value = false;
    Zp value;
    for (const auto& [mon, coef] : p) {
      if (coef != 0 && is_single_signal(mon)){
        auto [u, e] = *mon.begin();
        found_x = true;
        coef_x = coef;
        x = u;
      } else if (is_one(mon)){
        found_value = true;
        value = coef;
      } else{
        return result;
      }
    }
    if (found_value && found_x){
      result = {true, x, -value/coef_x};
    }
  }
  return result;
}

template <typename Coeff_Type>
pair<bool, vector<int>> is_or_constraint(const Polynomial<Coeff_Type> & p){
  vector<int> or_signals;

  if (p.size() != 1) return {false, or_signals};
   
  auto [mon, coef] = *p.begin();
  if (coef == 0 || mon.size() < 2) return {false, or_signals};

  for (const auto& [u, e] : mon) {
    if (e != 0) or_signals.push_back(u);
  }
  return {true, or_signals};
}

template <typename Coeff_Type>
pair<bool, int> is_binary_constraint(const Polynomial<Coeff_Type> & p){
  int possible_signal;
  bool found_x = false;
  bool found_xx = false;
  Zp found_coef;
  bool is_first = true;

  if (p.size() != 2){
    return {false, -1};
  } else{
    // Case two monomials, we need to study both of them
    for (const auto& [mon, coef]: p){
      if (is_first){
        found_coef = coef;
      } else if (found_coef != -coef){
        return {false, -1};
      }
        
      if (is_single_signal(mon)){
        found_x = true;
      } else if(is_quadratic_signal(mon)){
        found_xx = true;
      } else{
        return {false, -1};
      }
      int signal = *get_signals(mon).begin();
      if (is_first){
        possible_signal = signal;
      } else if (possible_signal !=  signal){
        return {false, -1};
      }
      is_first = false;
    }
  }
  if (found_x && found_xx){
    return {true, possible_signal};
  } else{
    return {false, -1};
  }
  
}


template <typename Coeff_Type>
pair<bool, set<int>> has_common_signal(const Polynomial<Coeff_Type> & p){
  set<int> possible_common_signal;
  bool found_first_non_linear = false;
  auto i = p.begin();
  while(i != p.end() && (!found_first_non_linear || !possible_common_signal.empty())){
    // only perform in the not linear part of the constraint
    if (is_nonlinear(i->first)){
      if (found_first_non_linear){
        set<int> aux;
        for(int signal: possible_common_signal){
          if (contains_signal(i->first, signal)){
            aux.insert(signal);
          }
        }
        possible_common_signal = aux;
      } else{
          possible_common_signal = get_signals(i->first);
         found_first_non_linear = true;
      }
    }
    i++;

  }
  
  // If we can extract multiple common factors? Try with all of them?

  if (possible_common_signal.empty()){
    return {false, possible_common_signal};
  } else{
    return {true, possible_common_signal};
  }
}


template <typename Coeff_Type>
pair<Polynomial<Coeff_Type>, Polynomial<Coeff_Type>> partition(const Polynomial<Coeff_Type> & p, int signal){
  Polynomial<Coeff_Type> pol_with_signal;
  Polynomial<Coeff_Type> pol_without_signal;
  auto i = p.begin();
  while(i != p.end()){
    auto [after_prop, degree] = perform_assignment(i->first, signal);
    Polynomial<Coeff_Type> to_add = Polynomial(i->second, after_prop);

    if (degree == 0){
      pol_without_signal = pol_without_signal + to_add;
    } else if (degree == 1){
      pol_with_signal = pol_with_signal + to_add;
    } else{
      Monomial missing_degrees = Monomial(signal, degree - 1);
      pol_with_signal = pol_with_signal + (missing_degrees * to_add);

    }
    i++;
  }
  return {pol_with_signal,  pol_without_signal};
}

template <typename Coeff_Type>
Polynomial<Coeff_Type> perform_assignment(const Polynomial<Coeff_Type> & p, int signal, Coeff_Type value){
  auto i = p.begin();
  Polynomial<Coeff_Type> new_p;
  while(i != p.end()){
    auto [after_prop, degree] = perform_assignment(i->first, signal);
    // to compute the power, better other way?
    // we need that the exponent is not 0
    Polynomial<Coeff_Type> to_add;
    if (degree == 0){
        to_add = Polynomial(i->second, i->first);
        new_p = new_p + to_add;
    } else if (value == 0){
        // no need to add anything  
    } else{
        Coeff_Type aux =  value;
        for (int j = 1; j < degree; j++){
          aux = aux * value;
        }
        to_add = Polynomial(i->second * aux, after_prop);
        new_p = new_p + to_add;
    }
    i++;
  }
  return new_p;
}

template <typename Coeff_Type>
Polynomial<Coeff_Type> perform_assignment_to_signal(const Polynomial<Coeff_Type> & p, int signal_eliminated, int signal_new){
  auto i = p.begin();
  Polynomial<Coeff_Type> new_p;
  while(i != p.end()){
    auto after_assignment = perform_assignment_to_signal(i->first, signal_eliminated, signal_new);
    Polynomial<Coeff_Type> to_add = Polynomial(i->second, after_assignment);
    new_p = new_p + to_add;
    
    i++;
  }
  return new_p;
}


template <typename Coeff_Type>
Polynomial<Coeff_Type> normalize_single(const Polynomial<Coeff_Type> & p){
  auto i = p.begin();
  Monomial signal;
  Coeff_Type coef_signal;
  Coeff_Type const_coeff = Coeff_Type(0);
  
  while (i != p.end()){
    if (i->first.size() == 0){ // case cte coefficient
      const_coeff = i->second;
    } else{
      signal = i->first;
      coef_signal = i->second;
    }
    i++;
  }
  Polynomial<Coeff_Type> result = Polynomial(Coeff_Type(1), signal); 
  if (const_coeff != Coeff_Type(0)){
    Coeff_Type new_coef = const_coeff / coef_signal;
    Polynomial aux = Polynomial(new_coef, Monomial());
    result = result + aux;
  }
  
  return result;

}

template <typename Coeff_Type>
set<int> get_signals(const Polynomial<Coeff_Type> & a){
  auto i = a.begin();
  set<int> signals;
  while(i != a.end()){
    set<int> mon_signals = get_signals(i->first);
    signals.insert(mon_signals.begin(), mon_signals.end());
    i++;
  }
  return signals;
}

template <typename Coeff_Type>
set<int> get_single_signals(const Polynomial<Coeff_Type> & a){
  auto i = a.begin();
  set<int> signals = get_signals(a);
  set<int> single_signals;

  for (int s: signals){
    auto [pol_s, pol_no_s] = partition(a, s);
    if (pol_s.size() == 1){
      auto [mon, coef] = *pol_s.begin();
      if(is_one(mon)){
        // single signal, study the coef
        if(coef == 1 || -coef == 1){
          single_signals.insert(s);
        }
      }
    }
  }

  return single_signals;
}


template<typename Coeff_Type>
vector<pair<vector<pair<int, int>>, Zp>> destruct_polynomial(const Polynomial<Coeff_Type> & a){
  vector<pair<vector<pair<int, int>>, Zp>>values;

  auto i = a.begin();

  while(i != a.end()){
    vector<pair<int, int>> aux;
    for (auto [s, exp]: i->first){
      aux.push_back({s, exp});
    }
    values.push_back({aux, i->second});
    i++;
  }
  return values;
}




template <typename Coeff_Type>
Polynomial<Coeff_Type>
operator +(const Polynomial<Coeff_Type>& a, const Polynomial<Coeff_Type>& b) {

  const auto& ca = a.mon2coeff;
  const auto& cb = b.mon2coeff;

  Polynomial<Coeff_Type> q;
  auto& m = q.mon2coeff;

  auto i = ca.begin();
  auto j = cb.begin();
    
  while (i != ca.end() and j != cb.end()) {
    if      (i->first < j->first) {m.insert(*i); ++i; }
    else if (i->first > j->first) {m.insert(*j); ++j; }
    else {
      Coeff_Type r = i->second + j->second;
      if (not is_zero(r)) m.insert({i->first, r});
      ++i;
      ++j;
    }
  }

  while (i != ca.end()) { m.insert(*i); ++i; }
  while (j != cb.end()) { m.insert(*j); ++j; }
  //cout << "Building polynomial" << q <<endl;
  // The roots are known only if it is a cte or a signal + cte = 0
  
  if (is_zero(a)){
     q.known_roots = b.known_roots;
     q.roots = b.roots;
  } else if (is_zero(b)){
     q.known_roots = a.known_roots;
     q.roots = a.roots;
  } else{
      auto [is_eq_cte, signal, value] = is_signal_eq_constant(q);
      if (is_eq_cte){
        //cout << "The roots are known " << signal << " ->" << value << endl;
        q.known_roots = true;
        q.roots = {{signal, value}};
      }
      else if(is_nonzero_constant(q) || is_zero(q)){
        q.known_roots = true;
        q.roots = {};
      } else{
        q.known_roots = false;
        q.roots = {};
      }
  }
  return q;
}


template <typename Coeff_Type>
Polynomial<Coeff_Type>
operator *(const Coeff_Type& a,
	   const Polynomial<Coeff_Type>& p) {

  if (is_zero(a)) return Polynomial<Coeff_Type>();
    
  const auto& cp = p.mon2coeff;
  Polynomial<Coeff_Type> q;
  auto& m = q.mon2coeff;
    
  auto i = cp.begin();
  while (i != cp.end()) {
    m.insert({i->first, a * i->second});
    ++i;
  }

  // The roots are the same as before. They are known if they were known before
  q.known_roots = p.known_roots;
  q.roots = p.roots;
  //cout << "Building polynomial" << q <<endl;
  //cout << "The roots are known " << q.known_roots << endl;

  return q;
}


template <typename Coeff_Type>
Polynomial<Coeff_Type>
operator *(const Monomial& a,
	   const Polynomial<Coeff_Type>& p) {

  if (is_one(a)) return p;

  const auto& cp = p.mon2coeff;

  Polynomial<Coeff_Type> q;
  auto& m = q.mon2coeff;
  
  auto i = cp.begin();
  while (i != cp.end()) {
    Monomial q = a * i->first;
    auto j = m.find(q);
    if (j == m.end()) m.insert({q, i->second});
    else {
      j->second += i->second;
      if (is_zero(j->second)) 
	m.erase(j);
    }
    ++i;
  }


  // The roots are known if they were known in p. 
  // If so, the roots are the roots in p and all signals in a with root 0 ()
  if (p.known_roots){
    q.known_roots = true;
    q.roots = p.roots;
    set<int> signals = get_signals(a);
    for (auto s: signals){
      q.roots.push_back({s, 0});
    }
  } else{
    q.known_roots = false;
    q.roots = {};
  }
      //cout << "Building polynomial" << q <<endl;
      //cout << "The roots are known " << q.known_roots << endl;

  return q;
}


template <typename Coeff_Type>
Polynomial<Coeff_Type>
operator *(const Polynomial<Coeff_Type>& a,
	   const Polynomial<Coeff_Type>& b) {

  Polynomial<Coeff_Type> r;
    
  const map<Monomial, Coeff_Type>& ca = a.mon2coeff;
 
  auto i = ca.begin();
  while (i != ca.end()) {
    r = r + (i->second * (i->first * b));
    ++i;
  }

  // The roots are known if they were known in both cases
  // If so, the roots are the concatenation of both roots
  if (a.known_roots && b.known_roots){
    r.known_roots = true;
    r.roots = a.roots;
    for (auto val: b.roots){
      r.roots.push_back(val);
    }
  } else{
    r.known_roots = false;
    r.roots = {};
  }
      //cout << "Building polynomial" << r <<endl;
      //cout << "The roots are known " << r.known_roots << endl;


  return r;
}

} // namespace FF

#endif // FF_POLYNOMIAL_HPP

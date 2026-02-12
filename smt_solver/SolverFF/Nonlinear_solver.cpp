#include "Nonlinear_solver.inlines.hpp"
#include "Solver.inlines.hpp"
#include "Square_rooter.hpp"

#include <assert.h>

#include <unordered_map>
#include "z3++.h"

/*#include <CoCoA/ring.H> //ring
#include <CoCoA/BigInt.H> //BigInt
#include <CoCoA/symbol.H> //symbol
#include <CoCoA/QuotientRing.H> //NewZZmod
#include <CoCoA/SparsePolyRing.H> //NewPolyRing
#include <CoCoA/SparsePolyOps-ideal.H> //GBasiS*/
#include "Solver.defs.hpp"
#include <string>
#include <vector>
#include <sstream>
#include <fstream>
#include "maplec.h"
using namespace FF;


void Nonlinear_solver::initializeAfterParsing() { }





/*CoCoA::RingElem fromPolyToRingELem(const Polynomial<Zp>& pol, const CoCoA::ring& polyRing, const CoCoA::ring& r,
                                    const std::vector<CoCoA::symbol>& symbols) {
    CoCoA::RingElem polynomial(polyRing, CoCoA::BigInt(0));
    for (const auto& [mon, coe] : pol) {
        // For each monomial, create the CoCoA::RingElem
        CoCoA::RingElem monomial = CoCoA::RingElem(r, 1);
        for (const auto& [u, e] : mon) {
            // For each variable in the monomial, multiply the monomial by the variable
            // to the power of the exponent.
            CoCoA::RingElem variable = CoCoA::RingElem(polyRing,symbols[u]);
            for (int i = 0; i < e; ++i) {
                monomial = monomial * variable;
            }
        }
        CoCoA::RingElem coeff(polyRing, CoCoA::BigIntFromMPZ(coe.get_v().get_mpz_t()));
        polynomial += monomial * coeff;
    }
    return polynomial;
}

//TO IMPROVE:
// * Instead of considering all symbols in the context, count the number of symbols used in s.getAssignment()
//                  Maybe if the symbols do not appear in the polynomials, then the efficiency is not affected.
// * We can generate symbols with each variable's original name.
void Nonlinear_solver::literals2cocoa_pols(std::vector<CoCoA::RingElem>& generators) {

  //First, we create the new QuotientRIng.
  CoCoA::QuotientRing coeffRing = CoCoA::NewZZmod(PRIME);

  //We count the number of negative literals, since we need to add a symbol for each.
  int numNegatives = std::count_if(s.getAssignment().begin(), s.getAssignment().end(), [](const Lit& lit) {
        return lit.isNegative();
    });

  int num_vars = s.get_num_vars();
  //We create the vector of symbols containg all the variables.
  std::vector<CoCoA::symbol> symbols = CoCoA::NewSymbols(num_vars + numNegatives);


  // Create the polynomial ring
  CoCoA::ring r(coeffRing);
  CoCoA::ring polyRing = CoCoA::NewPolyRing(r, symbols);

  int neg_index = 0;
  for(auto it_lit = s.getAssignment().begin(); it_lit != s.getAssignment().end(); ++it_lit) {
    //For each literal, create the corresponding CoCoA::RingElem
    auto num = var(*it_lit);
    auto pol = s.getPolynomial(num);
    CoCoA::RingElem polynomial = fromPolyToRingELem(pol, polyRing, r, symbols);

    if(it_lit->isNegative()){
      //We only need to add the polynomial to the list of generators: pol*var_neg = 1 => pol != 0.
      polynomial *= CoCoA::RingElem(r,symbols[num_vars + neg_index]);
      polynomial -= CoCoA::RingElem(r, CoCoA::BigInt(1));
      neg_index++;
    }
    //Add the polynomial to the list of generators
    polynomial = polynomial / CoCoA::LC(polynomial);
    generators.push_back(polynomial);
  }
}*/

/*
int Nonlinear_solver::checkConsistency_cocoa(int level) {
  //For each Polynomial in cons_db.poly2var we need
  //to create a cocoa polynomial and add it to generators.
  std::vector<CoCoA::RingElem> generators;
  literals2cocoa_pols(generators);

  CoCoA::ideal ideal = CoCoA::ideal(generators);
  std::vector<CoCoA::RingElem> basis = CoCoA::GBasis(ideal);

  bool is_trivial = basis.size() == 1 && CoCoA::deg(basis.front()) == 0;

  return 1;
}
*/

void Nonlinear_solver::setBTPoint() {

}


void Nonlinear_solver::backtrack(int n) {
}

Polynomial<Zp> parseMonomial(const std::string& token, bool positive, bool & contains_u);
Polynomial<Zp> fromStringToMonomial(const std::string& monomial, bool positive, bool & contains_u);

Polynomial<Zp> fromStringToPoly(string & polynomial, int ini, int end, bool & contains_u) { 
  // Example of polynomial: (1)*x_0^2 + (1)*x_1 + (2)*x_2*u_0 + (1)*u_1 + (3)
  Polynomial<Zp> pol; 
  //remove spaces
  std::istringstream stream(polynomial);
  std::string token;
  if(ini == end){
    return pol;
  } 
  bool positive;
//  std::cout << polynomial << endl;
  int next_ini = ini;
  if (polynomial[ini] == '+'){
    positive = true;
    next_ini = ini + 1;
  } else if(polynomial[ini] == 'x' || polynomial[ini] == 'u'){
      positive = true;
    }
    else if (polynomial[ini] == '-'){
    positive = false;
    next_ini = ini + 1;
  } else{
    positive = true;
    next_ini = ini;
  }
  //search for the next + or - sign in polynomial
  size_t next_pos = polynomial.find_first_of("+-", ini+1);
  if (next_pos == std::string::npos) {
    next_pos = end;
  }
  
  // Extract the current monomial
  std::string monomial = polynomial.substr(next_ini, next_pos - ini);
  // Create the corresponding polynomial term

  Polynomial<Zp> term = fromStringToMonomial(monomial, positive, contains_u);

  Polynomial<Zp> pol2 = fromStringToPoly(polynomial, next_pos, end, contains_u);
  pol = term + pol2;
  //std::cout << pol << endl;
  return pol;
}

Polynomial<Zp> parseMonomial(const std::string& token, bool positive, bool & contains_u) {
  // Parse each factor (e.g., x_1^2, u_0)
  Polynomial<Zp> factor;
  size_t caretPos = token.find('^');
  auto coef = Zp(1);
  if(!positive) coef = Zp(-1);
  //std:: cout << token << endl;
  if (caretPos != std::string::npos) {
      // Factor has an exponent
      //std::cout << token << endl;
      std::string varPart = token.substr(0, caretPos);
      int exponent = std::stoi(token.substr(caretPos + 1));
      if (varPart[0] == 'x') {
          int varIndex = std::stoi(varPart.substr(2)); // Skip "x_"
          factor = Polynomial<Zp>(coef, Monomial(varIndex, exponent));
      } else if (varPart[0] == 'u') {
          int varIndex = std::stoi(varPart.substr(2)); // Skip "u_"
          contains_u = true;
          factor = Polynomial<Zp>(coef, Monomial(varIndex, exponent)); // Offset for u variables
      } else {
          throw std::invalid_argument("Invalid variable format");
      }
  } else {
      //std::cout << token << endl;
      // Factor does not have an exponent
      if (token[0] == 'x') {
          int varIndex = std::stoi(token.substr(2)); // Skip "x_"
          factor = Polynomial<Zp>(coef, Monomial(varIndex, 1));
      } else if (token[0] == 'u') {
          int varIndex = std::stoi(token.substr(2)); // Skip "u_"
          contains_u = true;
          factor = Polynomial<Zp>(coef, Monomial(varIndex, 1)); // Offset for u variables
      } else { // Constant term
          //std::cout << token << endl;
          mpz_class constant = mpz_class(token);
          if(!positive) constant = -constant;
          factor = Polynomial<Zp>(Zp(constant)); 

      }
  }
  return factor;
}

Polynomial<Zp> fromStringToMonomial(const std::string& monomial, bool positive, bool & contains_u) {
    //Example: x_1^2*x_2*u_0 
    Polynomial<Zp> term = Polynomial<Zp>(Zp(1));
    std::istringstream stream(monomial);
    std::string token;

    while (std::getline(stream, token, '*')) {
        // Parse each factor (e.g., x_1^2, u_0)
        Polynomial<Zp> factor = parseMonomial(token, positive, contains_u);
        positive = true;
        term = term * factor;
    }
//    std::cout << term;
    return term;
}

/*
// La función toma el polinomio y devuelve un string con la representación del polinomio
std::string fromPolyToString(const Polynomial<Zp>& pol, set<string>& uniqueVariables) {
    std::ostringstream polynomialStream;

    // FF_OUT(NONLINEAR, "Polynomial: " << pol << std::endl);

    for (const auto& [mon, coe] : pol) {
        if (coe == 0) continue; // 

        polynomialStream << " + "; // Sep between monomials

        // Agregar el coeficiente, si no es 1 o -1, o si el monomio es constante
 
        polynomialStream << "(" << coe << ")"; // Coefficient

        if(mon.size() > 0){
          for (const auto& [u, e] : mon) {
              uniqueVariables.insert("x_" + std::to_string(u));
              polynomialStream <<  "*x_" << u;
              if (e > 1) {
                  polynomialStream << "^" << e;
              }
          }
        }
    }

    // FF_OUT(NONLINEAR, "Related Polynomial: " << polynomialStream.str() << std::endl);
    return polynomialStream.str();
}*/
pair<vector<Polynomial<Zp>>, vector<Polynomial<Zp>>> get_maple_groebner_basis(ifstream& inFile) {
    vector< Polynomial<Zp> > without_u;
    vector<Polynomial<Zp>> with_u;
    string line;
    bool contains_u = false;
    while(std::getline(inFile, line)) {
        //std::cout << "Read line: " << line << std::endl;
        // Convert each token back to a literal
        line.erase(remove(line.begin(), line.end(), ' '), line.end());
        Polynomial<Zp> pol = fromStringToPoly(line,0,line.size(), contains_u);
        // std::cout << "Processed polynomial: " << pol << std::endl;
        if(contains_u){
            with_u.push_back(pol);
        } else{
            without_u.push_back(pol);
        }
        contains_u = false;
    }
    return {without_u, with_u};
}

pair<std::vector< Polynomial<Zp> >, std::vector< Polynomial<Zp> > > get_cocoa_groebner_basis(const string & groebner_basis) {
  std::vector< Polynomial<Zp> > without_u;
  std::vector< Polynomial<Zp> > with_u;
  //remove initial [ and final ]
  std::string groebner_basis_clean = groebner_basis.substr(1, groebner_basis.size() - 2);
  //std::cout << groebner_basis_clean << std::endl;
  // Split the string by commas
  std::istringstream stream(groebner_basis_clean);
  std::string token;
  bool contains_u = false;
  while (std::getline(stream, token, ',')) {
    // Convert each token back to a literal
    token.erase(remove(token.begin(), token.end(), ' '), token.end());
    Polynomial<Zp> pol = fromStringToPoly(token,0,token.size(), contains_u);
    if(contains_u){
        with_u.push_back(pol);
    } else{
        without_u.push_back(pol);
    }
    contains_u = false;
    //std::cout << pol << endl;
  }
  return {without_u, with_u};
}

// La función toma el polinomio y devuelve un string con la representación del polinomio
std::string fromPolyToString(const Polynomial<Zp>& pol, set<string>& uniqueVariables) {
    std::ostringstream polynomialStream;

    // FF_OUT(NONLINEAR, "Polynomial: " << pol << std::endl);

    for (const auto& [mon, coe] : pol) {
        if (coe == 0) continue; // 

        polynomialStream << " + "; // Sep between monomials

        // Agregar el coeficiente, si no es 1 o -1, o si el monomio es constante
 
        polynomialStream << "(" << coe << ")"; // Coefficient

        if(mon.size() > 0){
          for (const auto& [u, e] : mon) {
              uniqueVariables.insert("x_" + std::to_string(u));
              polynomialStream <<  "*x_" << u;
              if (e > 1) {
                  polynomialStream << "^" << e;
              }
          }
        }
    }

    // FF_OUT(NONLINEAR, "Related Polynomial: " << polynomialStream.str() << std::endl);
    return polynomialStream.str();
}


vector< pair< Polynomial<Zp>,bool>> debug_assignment(int level){
      FF_OUT(NONLINEAR, "Test case" << std::endl);

  vector< pair< Polynomial<Zp>,bool>> assignment;

  if(level == 0){
    Monomial x_2 = {1,2};
    Monomial coef_1 = {0,0};
    Monomial x = {1,1};
    Polynomial<Zp> indep(1,coef_1);
    Polynomial<Zp> p(1,x_2);
    p = p + indep;
    
    Polynomial<Zp> p2(1,x);

    Polynomial<Zp> p3(2,x);

    //pols = [x² + 1, x, 2x]
    assignment.push_back({p,false});
    assignment.push_back({p2,false});
    assignment.push_back({p3,false});
  } 
  else if (level == 1) {
        Monomial x_2 = {1,2};
    Monomial coef_1 = {0,0};
    Monomial x = {1,1};
    Polynomial<Zp> indep(1,coef_1);
    Polynomial<Zp> p(1,x_2);
    p = p + indep;

    //pols = [x² + 1, x, 2x]
    assignment.push_back({p,false});
  } else {
        Monomial x_2 = {1,2};
    Monomial coef_1 = {0,0};
    Monomial x = {1,1};
    Polynomial<Zp> indep(1,coef_1);
    Polynomial<Zp> p(1,x_2);
    p = p + indep;
    
    Polynomial<Zp> p2(1,x);

    Polynomial<Zp> p3(2,x);

    //pols = [x² + 1, x, 2x]
    assignment.push_back({p,false});
    assignment.push_back({p2,false});
    assignment.push_back({p3,true});
  }

  return assignment;
}

void Nonlinear_solver::test(){


  std::cout << "Starting tests" << std::endl;

  int num_conflicts = checkConsistency(0);
	std::cout << num_conflicts << ", " << s.conf_exp.size() << std::endl;
  FF_ASSERT(NONLINEAR, num_conflicts == -2 && s.conf_exp.size() == 2);


  num_conflicts = checkConsistency(1);
	std::cout << num_conflicts << ", " << s.conf_exp.size() << std::endl;
  FF_ASSERT(NONLINEAR, num_conflicts == 0 && s.conf_exp.size() == 0);

  num_conflicts = checkConsistency(2);
	std::cout << num_conflicts << ", " << s.conf_exp.size() << std::endl;
  FF_ASSERT(NONLINEAR, num_conflicts == 0 && s.conf_exp.size() == 0);

  std::cout << "Test passed" << std::endl;
}

string Nonlinear_solver::produce_test_polynomials(int level){


  vector< pair< Polynomial<Zp>,bool>> assignment = debug_assignment(level);

  std::ostringstream result;
  int neg_index = 0;
  bool firstPoly = true;
  for(auto it_lit = assignment.begin(); it_lit != assignment.end(); ++it_lit) {
    if (!firstPoly) {
          result << ", "; // Sep between polynomials
    }
    firstPoly = false;

    Polynomial<Zp> pol = it_lit->first;

    set<string> uniqueVariables;
    string polynomial = fromPolyToString(pol, uniqueVariables);

    if(it_lit->second){
      //We only need to add the polynomial to the list of generators: pol*var_neg = 1 => pol != 0.
      polynomial = "(" + polynomial + ")*u_" + std::to_string(neg_index);
      mpz_class p(prime);
      mpz_class minus_one = p-1;
      polynomial = polynomial + " + " + minus_one.get_str();
      neg_index++;
    }
    //Add the polynomial to the list of generators
    result << polynomial;
  }

  return result.str();
}


void FF::literal2maple_pol(ostringstream& result, const Solver& s, Lit lit, set<string>& uniqueVariables) {

  auto num = var(lit);
  FF_ASSERT(NONLINEAR, num != 0);

  auto pol = s.getPolynomial(num);
  string polynomial = fromPolyToString(pol, uniqueVariables);

  if(lit.isNegative()){
    //We only need to add the polynomial to the list of generators: pol*var_neg = 1 => pol != 0.
    polynomial = "(" + polynomial + ")*u_" + std::to_string(s.get_num_vars() + 1 + uniqueVariables.size());
    mpz_class p(prime);
    mpz_class minus_one = p-1;
    polynomial = polynomial + " + " + minus_one.get_str();
    uniqueVariables.insert("u_" + std::to_string(s.get_num_vars() + 1 + uniqueVariables.size()));
  }
  //Add the polynomial to the list of generators
  result << polynomial;
}


// La función principal para concatenar polinomios como strings
pair<std::string, set<string>> Nonlinear_solver::literals2maple_pols() {
  
  std::ostringstream result;

  bool firstPoly = true;
  set<string> uniqueVariables;
  for(auto it_lit = s.getAssignment().begin(); it_lit != s.getAssignment().end(); ++it_lit) {

    Lit lit = *it_lit;
    if(lit == Lit()){
      continue;
    }

    if (!firstPoly) {
          result << ", "; // Sep between polynomials
    }
    firstPoly = false;

    literal2maple_pol(result, s, lit, uniqueVariables);
  }

  return {result.str(), uniqueVariables};
}


std::ofstream mapleOutputFile; // This file is used for communication between maple and the solver
//TO IMPROVE:
// ** Maybe we should keep the file open at any time. 

static void M_DECL textCallBack(void *data, int tag, const char *output) {
    mapleOutputFile << output << std::endl;  
    //Remove flush when debugging is done
    mapleOutputFile.flush();
}

Nonlinear_solver::~Nonlinear_solver() {
  if(maple_initialized){ 
     EvalMapleStatement(kv, "quit:");
     StopMaple(kv);
   }
  cerr << "Number of calls to Non-Linear Solver: " << num_queries << endl;  

}

struct Time_Stamp {
  double  acc;
  clock_t ini;
  string  msg;
   int verbose = 1;
  
  Time_Stamp(string msg) : acc(0), msg(msg) {}
  ~Time_Stamp() { if (verbose >= 0) cerr << "Accumulated time in <" << msg << ">: " << acc << " s." << endl;
 //                 cerr << "Number of calls to Non-Linear Solver: " << num_queries << endl;
 }
  void start() { ini = clock(); }
  double stop () {
    double secs = double(clock()- ini) / CLOCKS_PER_SEC;
    acc += secs;
    return secs;
  }
};

void Nonlinear_solver::initialize_maple(){
   if(!maple_initialized && using_maple){
     char err[2048];
     // auto time = Time_Stamp("maple initialization");
     // time.start();
     MCallBackVectorDesc cb = {  textCallBack,

                    0,

                    0,

                    0,

                    0,

                    0,

                    0,

                    0

                };


     kv=StartMaple(0,NULL,&cb,NULL,NULL,err);
     // time.stop();
    //time.~TimeStamp();
     if (kv== NULL ) {
        std::cerr << "Fatal error: " << err << std::endl;
        exit(EXIT_FAILURE);
     }
     maple_initialized = true;
  }
}

Nonlinear_solver::Nonlinear_solver(Solver& s, bool firstSATNRA, bool using_cocoa) :
    s(s), num_queries(0), maple_initialized(false), firstSATNRA(firstSATNRA) {
    using_maple = !using_cocoa;
   /*  char err[2048];
     maple_initialized = false;
    auto time = Time_Stamp("inicializar maple");
    time.start();
    std::cout << "Creando sesion" << std::endl;
    MCallBackVectorDesc cb = {  textCallBack,

                    0,

                    0,

                    0,

                    0,

                    0,

                    0,

                    0

                };


    kv=StartMaple(0,NULL,&cb,NULL,NULL,err);
    time.stop();
    //time.~TimeStamp();
    std::cout << "Sesion creada" << std::endl;
    if (kv== NULL ) {
        std::cerr << "Fatal error: " << err << std::endl;
        exit(EXIT_FAILURE);
    }*/
  }

  int Nonlinear_solver::checkConsistency_maple(int level);
  int Nonlinear_solver::checkConsistency_cocoa(int level);



std::pair<std::vector< Polynomial<Zp> >, std::vector< Polynomial<Zp> > > literals2pols(Solver& s) {
  std::vector< Polynomial<Zp> > pospols;
  std::vector< Polynomial<Zp> > negpols;
  
  for(auto it_lit = s.getAssignment().begin(); it_lit != s.getAssignment().end(); ++it_lit) {
    
    Lit lit = *it_lit;
    if(lit == Lit()){
      continue;
    }

    auto num = var(lit);
    FF_ASSERT(NONLINEAR, num != 0);
    auto pol = s.getPolynomial(num);
    if(lit.isNegative()){
      negpols.push_back(pol);
    } else {
      pospols.push_back(pol);
    }        
  }
  return {pospols, negpols}; 
}


z3::expr monomial2z3expression(const Monomial & m, z3::context &c, uint num_vars, std::map<string, int> & name2idx) {
  using namespace z3;
  expr res = c.real_val(1);
  for (auto i = m.begin(); i != m.end(); i++) {
    string name;
    if (i->first < num_vars) {
      name = get_var_name(FF::Context::Variable(i->first));
    } else {
      name = "u_" + std::to_string(i->first);
    }
    name2idx[name] = i->first;
    expr var = c.real_const(name.c_str());
    for (uint j = 0; j < i->second; j++) {
      res = res * var;
    }
  }
  return res;
}

z3::expr monomial2z3NIAexpression(const Monomial & m, z3::context &c, uint num_vars, std::map<string, int> & name2idx) {
  using namespace z3;
  expr res = c.int_val(1);
  for (auto i = m.begin(); i != m.end(); i++) {
    string name;
    if (i->first < num_vars) {
      name = get_var_name(FF::Context::Variable(i->first));
    } else {
      name = "u_" + std::to_string(i->first);
    }
    name2idx[name] = i->first;
    expr var = c.int_const(name.c_str());
    for (uint j = 0; j < i->second; j++) {
      res = res * var;
    }
  }
  return res;
}

  z3::expr polynomial2z3expression(const Polynomial<Zp> & p, z3::context &c, uint num_vars, std::map<string, int> & name2idx) {
  using namespace z3;
  expr res = c.real_val(0);
  for (auto i = p.begin(); i != p.end(); i++) {
    mpz_class val = (i->second).get_v();
    std::stringstream ss;
    ss << val;
    expr coeff = c.real_val(ss.str().c_str());
    res = res + coeff * monomial2z3expression(i->first,c,num_vars,name2idx);
  }
  return res;
}

  z3::expr polynomial2z3NIAexpression(const Polynomial<Zp> & p, z3::context &c, uint num_vars, std::map<string, int> & name2idx) {
  using namespace z3;
  expr res = c.int_val(0);
  for (auto i = p.begin(); i != p.end(); i++) {
    mpz_class val = (i->second).get_v();
    std::stringstream ss;
    ss << val;
    expr coeff = c.int_val(ss.str().c_str());
    res = res + coeff * monomial2z3NIAexpression(i->first,c,num_vars,name2idx);
  }
  return res;
}

bool is_zp_expr(z3::expr n, Zp & z) {
  using namespace z3;
  string  vn;
  string  vd;
  n.numerator().is_numeral(vn);
  n.denominator().is_numeral(vd);
  Zp num(vn);
  Zp den(vd);
  if (vd != 0) {
    z  = vn/vd;
    return true;
  }
  return false;
}

bool is_zp_expr_NIA(z3::expr n, Zp & z) {
  using namespace z3;
  string  vn;
  if (n.is_numeral(vn)) {
    Zp zaux(vn);
    z = zaux;
    //cout << n << " --> " << vn << " --> " << z << endl;
    return true;
  }
  return false;
}

bool get_model_in_NRA(vector<Polynomial<Zp>> ppols, vector<Polynomial<Zp>> npols, Solver& s, uint timeout = 1000000, bool repeat = true, bool add_k = false) {
  using namespace z3;
  std::map<string, int> name2idx;
  context z3c;
  solver z3solver(z3c);
  z3solver.set("timeout", timeout);
  int i = 0;
  for(auto p : ppols){
    //cout << i++ << ": " << p << endl;
    expr poly_exp = polynomial2z3expression(p,z3c, s.get_num_vars(), name2idx);
    if (add_k) {
      string k_var_name = "_mk_"+ std::to_string(poly_exp.id());
      expr k_var = z3c.int_const(k_var_name.c_str());
      z3solver.add(poly_exp == k_var * z3c.int_val(prime.c_str()));
    } else {
      z3solver.add(poly_exp == 0);
    }
  }
  for(auto p : npols){
    //cout << i++ << ": " << p << endl;
    expr poly_exp = polynomial2z3expression(p,z3c, s.get_num_vars(), name2idx);
    /*if (add_k) {
      string k1_var_name = "_mk1_"+ std::to_string(poly_exp.id());
      string k2_var_name = "_mk2_"+ std::to_string(poly_exp.id());
      expr k1_var = z3c.real_const(k1_var_name.c_str());
      expr k2_var = z3c.real_const(k1_var_name.c_str());
      z3solver.add(poly_exp = k1_var * z3c.real_val(prime.c_str()) + k2_var);
      z3solver.add(k2_var != 0);
      z3solver.add(k2_var > -z3c.real_val(prime.c_str()));
      z3solver.add(k2_var < z3c.real_val(prime.c_str()));
    } else {*/
    z3solver.add(poly_exp != 0);
    //}
  }
  // cout << z3solver.to_smt2() << endl;
  int resla = z3solver.check();
  while (resla == sat) {
    cout << "Model found" << endl;
    model m = z3solver.get_model();
    uint n = m.num_consts();
    for (uint i = 0; i < n; i++) {
      auto sc = m.get_const_decl(i);
      if (name2idx.find(sc.name().str()) != name2idx.end() && name2idx[sc.name().str()] < s.get_num_vars()) {
        expr v = m.get_const_interp(sc);
        // cout << sc.name().str() << " -> " << v << endl;
        FF_ASSERT(NONLINEAR, v.is_numeral() || v.is_algebraic());
        if (v.is_numeral()) {
          Zp z;
          if (is_zp_expr(v, z)) {
            s.solution[sc.name().str()] = z;
            // cout << sc.name().str() << " -> " <<  s.solution[sc.name().str()] << endl;
          } else {
            cout << "Some denominator is zero: " << sc.name().str() << endl;
            if (repeat) break;
            else  return false;
          }            
        }
        else {
          cout << "Some value is algebraic: " <<endl;
          auto coefs = v.algebraic_poly();
          if  (coefs.size() <= 3) {
            assert(v.algebraic_i () >= 1 && v.algebraic_i () <= 2);
            cout << "it is the " << v.algebraic_i () << " square root" << endl;
            expr c = coefs[0];
            expr b = z3c.real_val(0);
            if (coefs.size() > 1) {b = coefs[1];}
            expr a = z3c.real_val(0);
            if (coefs.size() > 2) {a = coefs[2];}
            // cout << a << "x^2 + " << b << "x + " << c << endl;
            Zp za, zb, zc;
            if (is_zp_expr(a, za) && is_zp_expr(b, zb) &&is_zp_expr(c, zc)) {
              // cout << za << "x^2 + " << zb << "x + " << zc << endl;
              if (za == 0) {
                if (zb == 0) {
                  cout << "It has no solution" <<endl;
                  if (repeat) break;
                  else  return false;
                } else {
                  s.solution[sc.name().str()] = -zc/zb;;
                }
              } else {
                Zp nza = za; //za/zb;
                Zp nzb = zb; //zb/zb;                
                Zp nzc = zc; // zc/zb;
                //cout << nza << "x^2 + " << nzb << "x + " << nzc << endl;
                Zp b2m4ac = nzb*nzb - 4*nza*nzc;
                // cout << b2m4ac << endl;
                if (s.rooter.is_square(b2m4ac)) {
                  Zp sr_b2m4ac =  s.rooter.square_root(b2m4ac);
                  if (v.algebraic_i () == 2) {
                    sr_b2m4ac = -sr_b2m4ac;
                  }
                  s.solution[sc.name().str()] = (-nzb + sr_b2m4ac)/(2*nza);                  
                } else {
                  cout << "It has no square root" <<endl;
                  if (repeat) break;
                  else  return false;
                }
              }
            } else {
              cout << "Some denominator is zero: " << endl;
              if (repeat) break;
              else  return false;
            }
          } else {
            cout << "It is not a square root" <<endl;
            if (repeat) break;
            else  return false;
          }
        }
      }
    }
    FF_OUT(SOLVER, "NRA model found" << endl);
    if (s.assignment_is_satisfied(s.solution)) {
      return true;
    } else {
      
      if (!repeat) return false;
    }
    expr_vector negation(z3c);
    for (uint i = 0; i < n; i++) {
      auto sc = m.get_const_decl(i);
      if (name2idx[sc.name().str()] < s.get_num_vars()) {
        expr v = m.get_const_interp(sc);
        negation.push_back(z3c.real_const(sc.name().str().c_str()) != v);
      }
    }
    expr neg = mk_or(negation);
    //cout << "Added negation: " << neg << endl;
    cout << "Find another model..." << endl;
    z3solver.add(neg);
    /*
    expr_vector ev = z3solver.assertions();
    for (uint i = 0; i < ev.size()/2; i++) {
      expr aux = ev[i];
      ev[i] = ev[ev.size() - i];
      ev[ev.size() - i] = aux;
    }
    z3solver.reset();
    z3solver.add(ev);
    */
    resla = z3solver.check();
  } 
  cout << "Solver result: " << resla << endl; 
  return false;
}

bool get_model_in_NIA(vector<Polynomial<Zp>> ppols, vector<Polynomial<Zp>> npols, Solver& s, uint timeout = 1000000, bool repeat = true, bool add_k = true) {
  using namespace z3;
  std::map<string, int> name2idx;
  context z3c;
  solver z3solver(z3c);
  z3solver.set("timeout", timeout);
  int i = 0;
  for(auto p : ppols){
    //cout << i++ << ": " << p << endl;
    expr poly_exp = polynomial2z3NIAexpression(p,z3c, s.get_num_vars(), name2idx);
    if (add_k) {
      string k_var_name = "_mk_"+ std::to_string(poly_exp.id());
      expr k_var = z3c.int_const(k_var_name.c_str());
      z3solver.add(poly_exp == k_var * z3c.int_val(prime.c_str()));
    } else {
      z3solver.add(poly_exp == 0);
    }
  }
  for(auto p : npols){
    //cout << i++ << ": " << p << endl;
    expr poly_exp = polynomial2z3NIAexpression(p,z3c, s.get_num_vars(), name2idx);
    if (add_k) {
      string k1_var_name = "_mk1_"+ std::to_string(poly_exp.id());
      string k2_var_name = "_mk2_"+ std::to_string(poly_exp.id());
      expr k1_var = z3c.int_const(k1_var_name.c_str());
      expr k2_var = z3c.int_const(k2_var_name.c_str());
      z3solver.add(poly_exp == k1_var * z3c.int_val(prime.c_str()) + k2_var);
      z3solver.add(k2_var != 0);
      z3solver.add(k2_var > -z3c.int_val(prime.c_str()));
      z3solver.add(k2_var < z3c.int_val(prime.c_str()));
    } else {
      z3solver.add(poly_exp != 0);
    }
  }
  // cout << z3solver.to_smt2() << endl;
  int resla = z3solver.check();
  while (resla == sat) {
    cout << "Model found" << endl;
    model m = z3solver.get_model();
    uint n = m.num_consts();
    for (uint i = 0; i < n; i++) {
      auto sc = m.get_const_decl(i);
      if (name2idx.find(sc.name().str()) != name2idx.end() && name2idx[sc.name().str()] < s.get_num_vars()) {
        expr v = m.get_const_interp(sc);
        // cout << sc.name().str() << " -> " << v << endl;
        FF_ASSERT(NONLINEAR, v.is_numeral() || v.is_algebraic());
        if (v.is_numeral()) {
          Zp z;
          if (is_zp_expr_NIA(v, z)) {
            s.solution[sc.name().str()] = z;
            //cout << sc.name().str() << " -> " <<  s.solution[sc.name().str()] << endl;
          } else {
            cout << "Some denominator is zero: " << sc.name().str() << endl;
            if (repeat) break;
            else  return false;
          }            
        }
        else {
            if (repeat) break;
            else  return false;
        }
      }
    }
    FF_OUT(SOLVER, "NIA model found" << endl);
    if (s.assignment_is_satisfied(s.solution)) {
      return true;
    } else {
      
      if (!repeat) return false;
    }
    expr_vector negation(z3c);
    for (uint i = 0; i < n; i++) {
      auto sc = m.get_const_decl(i);
      if (name2idx[sc.name().str()] < s.get_num_vars()) {
        expr v = m.get_const_interp(sc);
        negation.push_back(z3c.real_const(sc.name().str().c_str()) != v);
      }
    }
    expr neg = mk_or(negation);
    //cout << "Added negation: " << neg << endl;
    cout << "Find another model..." << endl;
    z3solver.add(neg);
    /*
    expr_vector ev = z3solver.assertions();
    for (uint i = 0; i < ev.size()/2; i++) {
      expr aux = ev[i];
      ev[i] = ev[ev.size() - i];
      ev[ev.size() - i] = aux;
    }
    z3solver.reset();
    z3solver.add(ev);
    */
    resla = z3solver.check();
  } 
  cout << "Solver result: " << resla << endl; 
  return false;
}


// This version uses Maple with its API.
int Nonlinear_solver::checkConsistency(int level) {
  if(firstSATNRA){
    cout << "Trying before GB" << endl;
    auto [pospols, negpols] = literals2pols(s);
    if (get_model_in_NRA(pospols,negpols,s,100000,false)) {
    //if (get_model_in_NRA(pospols,negpols,s,100000,false, true)) {
      cout << "Valid NRA model" << endl;
      return 0;
    } else {
      cout << "NO or incorrect NRA model" << endl;
      /*cout << "Trying before GB with NIA and k" << endl;
      if (get_model_in_NIA(pospols,negpols,s,100000,false)) {
        cout << "Valid NIA model" << endl;
        return 0;
      } else {
        cout << "NO or incorrect NIA model" << endl;
      }*/
    }
  }
  cout << "Calling GB" << endl;
  if(using_maple){
    return checkConsistency_maple(level);
  } else {
    return checkConsistency_cocoa(level);
  }
}

int Nonlinear_solver::checkConsistency_cocoa(int level) {
    num_queries++;
    FF_OUT(NONLINEAR, "Checking consistency #" << num_queries << std::endl);
    
    std::ofstream cocoaInputFile; // This file is used for communication between cocoa and the solver
    
    uint64_t __ff_rand = std::time(nullptr);
    std::string random_suffix = "_" + std::to_string(__ff_rand);
    std::string cocoaInputFilename = "./cocoa_input" + random_suffix + ".cocoa";
    cocoaInputFile.open(cocoaInputFilename, std::ios_base::out);
    if (!cocoaInputFile.is_open()) {
      std::cout << "Unable to open file" << std::endl;
      return 1;
    }

    //check if command cocoa is available in the system
    //FF_ASSERT(NONLINEAR, ("command -v ../cocoa/cocoa-5.4/bin/CoCoAInterpreter > /dev/null 2>&1") == 0);

    auto [polynomials_str, uniqueVariables] = literals2maple_pols();
    // std::cout << polynomials_str << endl; 
    auto it = uniqueVariables.begin();
    //write the cocoa input file
    cocoaInputFile << "Use R ::= ZZ/(" << prime<< ")[" << *it;
    ++it;
    for( ; it != uniqueVariables.end(); ++it){
      cocoaInputFile << ", " << *it;
    }
    cocoaInputFile << "];" << std::endl;
    cocoaInputFile << "I := ideal(" << polynomials_str << ");" << std::endl;
    cocoaInputFile << "G := GBasis(I);" << std::endl << "G;" << std::endl;
    cocoaInputFile << "GenRepr(1,I);" << std::endl;

    cocoaInputFile.close();

    std::string cocoaOutputFilename = "./cocoa_output" + random_suffix + ".txt";
    system(string("cocoa5 " + cocoaInputFilename + " > " + cocoaOutputFilename + " 2>error.txt").c_str());


    std::ifstream cocoaOutputFile; // This file is used for communication between cocoa and the solver

    cocoaOutputFile.open(cocoaOutputFilename, std::ios_base::out);
    if (!cocoaOutputFile.is_open()) {
      std::cout << "Unable to open file" << std::endl;
      return 1;
    }
  

    //Process last line of the file
    std::string lastLine, line, secondLastLine;
    while (std::getline(cocoaOutputFile, line)) {
      secondLastLine = lastLine;
      lastLine = line;
    }
    FF_OUT(NONLINEAR, "Cocoa output last line: " << lastLine << std::endl);
    if (lastLine == "[]") {
      // std::cout << "secondLastLine is: " << secondLastLine << std::endl;
      auto [without_u, with_u] = get_cocoa_groebner_basis(secondLastLine);
      int count = 0; 
      bool found = false;
      /*std::cout << secondLastLine << std::endl;
      std::cout << "Polynomials with u: " << std::endl;
      for(auto p : with_u){
          std::cout << p << endl;
      }
      std::cout << "Polynomials without u: " << std::endl;
      for(auto p : without_u){
          std::cout << p << endl;
      }*/ 
      for(auto p : without_u){
	      if (is_linear(p)) {
                vector<Lit> lits = s.getAssignment();
                Lit lit_pol = s.generate_literal_from_polynomial(p).first;
                lits.push_back(lit_pol);
                // add the new clause
                int res = s.process_new_clause(lits);
                if      (res  < 0) throw std::runtime_error("Error processing new clause");
                else if (res == 0) ++count;
                else if (res == 1) found = true;
        }
        else{
            count += s.performDeductionsFromPolynomial(p,s.getAssignment(),found);
        }
      }
      // std::cout << "The number of deductions is: " << count << endl;
      cocoaOutputFile.close();
      if (count == 0 && firstSATNRA) {
        std::cout << "Searching for NRA model..." << std::endl;
        vector<Polynomial<Zp>> pols;
        pols.insert(pols.end(), without_u.begin(), without_u.end());
        pols.insert(pols.end(), with_u.begin(), with_u.end());
        if (get_model_in_NRA(pols,{},s)) {
        //if (get_model_in_NRA(pols,{},s,true,true)) {
          // cout << "returning sat ..." << endl;
          return 0;
        } else {
          auto [pospols, negpols] = literals2pols(s);
          if (get_model_in_NRA(pospols,negpols,s)) {
          //if (get_model_in_NRA(pospols,negpols,s,true,true)) {
            return 0;
          }
        }
      }
      return 1;
    } 

    //we separate lastLine of the form [1, x, 0, x] into its components
    //remove [ and  ]
    lastLine = lastLine.substr(1, lastLine.size() - 2);
    //we split by ,
    std::istringstream ss(lastLine);
    std::string token;
    std::vector<std::string> tokens;
    while (std::getline(ss, token, ',')) {
      //we remove space in token
      token.erase(remove_if(token.begin(), token.end(), [](unsigned char c){ return std::isspace(c); }), token.end());
      tokens.push_back(token);
    }

    s.conf_exp.clear();

    auto& literal_assignment = s.getAssignment();

    int i = 0;
    for (Lit lit : literal_assignment) {
      if (lit != Lit()) {
        FF_ASSERT(NONLINEAR, not cocoaOutputFile.eof());
        if(tokens[i] != "0") { 
		        s.conf_exp.push_back(lit);
        }
        i++;
      }
    }

    cocoaOutputFile.close();
    return -s.conf_exp.size();
}

int Nonlinear_solver::checkConsistency_maple(int level) {

  // For each Polynomial in cons_db.poly2var we need
  // to create a Maple polynomial.
  initialize_maple();
  num_queries++;
	
  FF_OUT(NONLINEAR, "Checking consistency #" << num_queries << std::endl);
  
  uint64_t __ff_rand = std::time(nullptr);
  std::string random_suffix = "_" + std::to_string(__ff_rand);

  std::string mapleOutputFilename = std::string("./maple_output") + random_suffix + ".txt";
  std::string mapleFilterFilename = std::string("./maple_filter") + random_suffix + ".txt";


  mapleOutputFile.open(mapleOutputFilename, std::ios_base::out);
  if (!mapleOutputFile.is_open()) {
    std::cout << "Unable to open file" << std::endl;
    return 1;
  }

  FF_ASSERT(NONLINEAR, kv != NULL);

  auto [polynomials_str,_] = literals2maple_pols(); 

  stringstream list_of_polynomials;
  list_of_polynomials << "polys := [" << polynomials_str << "]:";

  stringstream groebner_basis;
  groebner_basis << "b := Basis(polys, tord" << num_queries <<", characteristic=" << prime << ", output=extended):";    
    
  string final_query = "if member(1,b[1]) then  print(member(1,b[1])); for i to nops(b[2][1]) do if b[2][1][i] <> 0 then print(1); else print(0); end if; end do; else print(member(1,b[1])); for i to nops(b[1]) do print(b[1][i]) end do; end if;";  

  FF_OUT(NONLINEAR, "Maple full query: \n with(Groebner): \n" << list_of_polynomials.str() << "\n" << groebner_basis.str() <<  "\n" << final_query  << "\n");

  EvalMapleStatement(kv, "with(Groebner):");
  EvalMapleStatement(kv, list_of_polynomials.str().c_str());
  EvalMapleStatement(kv, groebner_basis.str().c_str());
  EvalMapleStatement(kv, final_query.c_str());
    
  mapleOutputFile.close();
  
  system(string("grep --invert-match \"kilobytes\" " +
		mapleOutputFilename + " > " + mapleFilterFilename).c_str());
    
  std::ifstream inFile(mapleFilterFilename);
  if (!inFile.is_open()) {
    std::cout << "Unable to open file" << std::endl;
    return 1;
  }
    
  string isTrivial;
  while(inFile >> isTrivial && isTrivial != "false" && isTrivial != "true");
 
  s.conf_exp.clear();
  string pol;
  if (isTrivial == "false") {
    auto [without_u, with_u] = get_maple_groebner_basis(inFile);
    int count = 0; bool found = false;

    for(auto p : without_u){
      if (is_linear(p)) {
                vector<Lit> lits = s.getAssignment();
                Lit lit_pol = s.generate_literal_from_polynomial(p).first;
                // cout << "Deduced lineal polynomial: " << p << endl;
                lits.push_back(lit_pol);
                // add the new clause
                int res = s.process_new_clause(lits);
                if      (res  < 0) throw std::runtime_error("Error processing new clause");
                else if (res == 0) ++count;
                else if (res == 1) found = true;
        } else{
            count += s.performDeductionsFromPolynomial(p,s.getAssignment(),found);
        }
    }
    std::cout << "The number of deductions is: " << count << std::endl;
    inFile.close();
    if (count == 0 && firstSATNRA) {
        std::cout << "Searching for NRA model..." << std::endl;
        vector<Polynomial<Zp>> pols;
        pols.insert(pols.end(), without_u.begin(), without_u.end());
        pols.insert(pols.end(), with_u.begin(), with_u.end());
        std::cout << "Trying with the Groebner base..." << std::endl;
        if (get_model_in_NRA(pols,{},s)) {
          // cout << "returning sat ..." << endl;
          return 0;
        } else {
          auto [pospols, negpols] = literals2pols(s);
          std::cout << "Trying with the current literals..." << std::endl;
          if (get_model_in_NRA(pospols,negpols,s)) {
            return 0;
          }
        }
     }
    return 1;
  }

  auto& literal_assignment = s.getAssignment();

  for (Lit lit : literal_assignment) {
    if (lit != Lit()) {
      FF_ASSERT(NONLINEAR, not inFile.eof());
      int coef;
      inFile >> coef;
      if(coef == 1) s.conf_exp.push_back(lit);
    }
  }

  inFile.close();
  return -s.conf_exp.size();
}


/*
// This version uses Maple with system calls.
int Nonlinear_solver::checkConsistency(int level) {

  // For each Polynomial in cons_db.poly2var we need
  // to create a Maple polynomial.

  num_queries++;
  
  FF_OUT(NONLINEAR, "Checking consistency #" << num_queries << endl);
  string mapleInputFilename  = "./maple_input.txt";
  string mapleOutputFilename = "./maple_output.txt";
  string mapleFilterFilename = "./maple_filter.txt";

  stringstream list_of_polynomials;
  list_of_polynomials << "polys := [" << literals2maple_pols() << "]:";

  stringstream groebner_basis;
  groebner_basis << "b := Basis(polys, tord" << num_queries <<", characteristic=" << prime << ", output=extended):";    

  string final_query = "fprintf(f, \"%a\\n\", member(1, b[1])); for i to nops(b[2][1]) do if b[2][1][i] <> 0 then fprintf(f, \"%d\\n\", 1); else fprintf(f, \"%d\\n\", 0); end if; end do; fprintf(f, \"\\n\");";    
  
  ofstream out(mapleInputFilename);
  FF_ASSERT(NONLINEAR, out.is_open());
  string indent(4, ' ');
  out
    << "\n"
    << indent << "with(Groebner):"         << "\n"
    << indent << list_of_polynomials.str() << "\n"
    << indent << groebner_basis.str()      << "\n"
    << indent << "f := fopen(\"" << mapleOutputFilename << "\", 'WRITE', 'TEXT'):" << "\n"
    << indent << final_query               << "\n"
    << indent << "fclose(f):"              << "\n";
  out.close();

#if FF_PRINT  
  system(string("cat " + mapleInputFilename).c_str()); // Only for debugging purposes.
#endif

  system(string("maple -q < " + mapleInputFilename + " > /dev/null 2>&1").c_str());  
  system(string("grep --invert-match \"kilobytes\" " + mapleOutputFilename + " > " + mapleFilterFilename).c_str());

  ifstream inFile(mapleFilterFilename);
  if (!inFile.is_open()) {
    cout << "Unable to open file" << endl;
    return 1;
  }
    
  string isTrivial;
  inFile >> isTrivial;
  FF_ASSERT(NONLINEAR, isTrivial == "false" or isTrivial == "true");
 
  s.conf_exp.clear();

  if (isTrivial == "false") {
    inFile.close();
    return 1;
  }

  auto& literal_assignment = s.getAssignment();

  for (Lit lit : literal_assignment) {
    if (lit != Lit()) {
      FF_ASSERT(NONLINEAR, not inFile.eof());
      int coef;
      inFile >> coef;
      if(coef == 1) s.conf_exp.push_back(lit);
    }
  }
  inFile.close();
  return -s.conf_exp.size();
}
*/

#ifndef FF_CONTEXT_HPP
#define FF_CONTEXT_HPP

#include "Global.hpp"

namespace FF {


inline void set_context(Context& ctxt) {
  p_ctxt = &ctxt;
}


class Context {


private:

  vector<string>   idx2name; // index -> name.
  map<string, int> name2idx; // name -> index.


public:

  const map<string, int>& name_to_index() const { return name2idx; }

  int get_num_vars() const{
    return idx2name.size();
  }
  
  int index(string name) {
    auto [it, added] = name2idx.insert({name, idx2name.size()});
    if (added) idx2name.push_back(name);
    return it->second;
  }


  // There can be "unnamed" variables,
  // whose index is beyond the position of the last named variable.
  // Unnamed variables are meant to be artificial, not present in the formula.
  
  struct Variable {

    Variable(int idx) : idx(idx) { }

    friend ostream& operator <<(ostream& out, Variable v) {
      FF_ASSERT(CONTEXT, v.idx >= 0);
      int sz = p_ctxt->idx2name.size();
      if (v.idx >= sz)         // Extension for unnamed variables.
	out << "$" << v.idx - sz;
      else 
	out << p_ctxt->idx2name[v.idx];
      return out;
    }

    friend string get_var_name(Variable v){
      FF_ASSERT(CONTEXT, v.idx >= 0);
      int sz = p_ctxt->idx2name.size();
      if (v.idx >= sz)         // Extension for unnamed variables.
	      return "$" + (v.idx - sz);
      else 
	      return p_ctxt->idx2name[v.idx];
    }

    int idx;
  };

  friend ostream& operator <<(ostream& out, Context::Variable v);
  friend string get_var_name(Context::Variable v);

  Context() {
    set_context(*this);
  }
    
};

} // namespace FF
  
#endif // FF_CONTEXT_HPP

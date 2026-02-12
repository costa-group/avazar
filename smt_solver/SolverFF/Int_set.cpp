#include "Int_set.inlines.hpp"

using namespace FF;


void Int_set::clear(void) {

  for (int k = 0, size = support.size(); k < size; k++)
    pointer[support[k]] = WRONG_INDEX;

  support.clear();
}


ostream& FF::operator<<(ostream& out, const Int_set& s) {
  out << "{ ";
  for (auto i = s.beg(), end = s.end(); i != end; i.next(s))
    out << s.value(i) << " ";
  out << "}";
  return out;
}

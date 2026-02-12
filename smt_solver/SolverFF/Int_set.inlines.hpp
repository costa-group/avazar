#ifndef FF_INT_SET_INLINES_HPP
#define FF_INT_SET_INLINES_HPP

#include "Global.hpp"
#include "Vec.inlines.hpp"
#include "Int_set.defs.hpp"

namespace FF {

inline
Int_set::Iterator::Iterator(int i)
  : iter(i) {
}


inline
Int_set::Iterator::Iterator(const Iterator& i)
  : iter(i.iter) {
}


inline void
Int_set::Iterator::operator=(const Iterator& i) {
  iter = i.iter;
}


inline void
Int_set::Iterator::next(const Int_set& m) {
  iter--;
}


inline bool
Int_set::Iterator::operator==(Iterator i) const {
  return (iter == i.iter);
}


inline bool
Int_set::Iterator::operator!=(Iterator i) const {
  return (iter != i.iter);
}


inline Int_set::Int_set() {
}


inline Int_set::Int_set(int upp) {
  
  enlarge_range(upp);
}



inline Int_set::Int_set(const Int_set& s) :
  support(s.support),
  pointer(s.pointer) {

}


inline void Int_set::operator =(Int_set& s) {
  pointer = s.pointer;
  support = s.support;
}


inline void
Int_set::enlarge_range(int d) {
  
  for (int i = 0; i < d; i++)
    pointer.push(WRONG_INDEX);
}


inline void
Int_set::reduce_range(int d) {
  pointer.shrink(d);
}


inline int
Int_set::top() const {
  return pointer.size();
}


inline void
Int_set::insert(int x) {

  FF_ASSERT(INT_SET, x >= 0 && x < top());
  FF_ASSERT(INT_SET, !contains(x));

  pointer[x] = support.size();
  support.push(x);
}


inline void
Int_set::remove(int x) {

  FF_ASSERT(INT_SET, contains(x));
  FF_ASSERT(INT_SET, x >= 0 && x < pointer.size());

  int address = pointer[x];
  int last = support.top();
  pointer[last] = address;
  support.remove(address);
  pointer[x] = WRONG_INDEX;
}


inline bool
Int_set::contains(int x) const {
  FF_ASSERT(INT_SET, x >= 0 && x < pointer.size());

  return pointer[x] != WRONG_INDEX;
}


inline bool
Int_set::is_empty() const {
  return support.size() == 0;
}


inline int
Int_set::size() const {
  return support.size();
}


inline Int_set::Iterator
Int_set::beg() const {
  return Iterator(support.size() - 1);
}


inline Int_set::Iterator
Int_set::end() const {
  return Iterator(-1);
}


inline int
Int_set::value(Iterator i) const {

  FF_ASSERT(INT_SET, i.iter >= 0 && i.iter < support.size());

  return support[i.iter];
}


}
// namespace FF

#endif // FF_INT_SET_INLINES_HPP

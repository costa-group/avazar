#ifndef FF_ITERATOR_INLINES_HPP
#define FF_ITERATOR_INLINES_HPP

#include "Iterator.defs.hpp"

namespace FF {


// Member functions of class Simple_iterator.

inline Simple_iterator::Simple_iterator(void)  : iter(-1) { }

inline Simple_iterator::Simple_iterator(int i) : iter(i)  { }

inline Simple_iterator::Simple_iterator(const Simple_iterator& i)
  : iter(i.iter) {
}

inline void
Simple_iterator::operator =(const Simple_iterator& i) {
  iter = i.iter;
}

inline bool 
operator ==(Simple_iterator i, Simple_iterator j) {
  return (i.iter == j.iter);
}

inline bool
operator !=(Simple_iterator i, Simple_iterator j) {
  return !(i == j);
}

inline ostream& 
operator <<(ostream& out, Simple_iterator i) {
  out << "< " << i.iter << " >";
  return out;
}


// Member functions of class Complex_iterator.

inline Complex_iterator::Complex_iterator(void) 
  : base(0), offset(0) {
}

inline Complex_iterator::Complex_iterator(int bs, int off) 
  : base(bs), offset(off) {
}

inline 
Complex_iterator::Complex_iterator(const Complex_iterator& i) 
  : base(i.base), offset(i.offset) {
} 

inline void
Complex_iterator::operator =(const Complex_iterator& i) {
  base   = i.base;
  offset = i.offset;
}

inline bool
operator ==(const Complex_iterator& i, const Complex_iterator& j) {
  return (i.base == j.base && i.offset == j.offset);
}

inline bool
operator !=(const Complex_iterator& i, const Complex_iterator& j) {
  return !(i == j);
}

inline ostream& 
operator <<(ostream& out, const Complex_iterator& i) {
  out << "< " << i.base << ", " << i.offset << " >";
  return out;
}


// Member functions of class Row_iterator.

inline Row_iterator::Row_iterator(void) 
  : Simple_iterator(-1), ref(-1) {
} 

inline Row_iterator::Row_iterator(int refer, int i) 
  : Simple_iterator(i), ref(refer) {
} 

inline ostream& operator <<(ostream& out, Row_iterator i) {
  out << "< " << i.ref << ", " << i.iter << " >";
  return out;
}


// Member functions of class Col_iterator.

inline Col_iterator::Col_iterator(void) 
  : Simple_iterator(-1), ref(-1) {
} 

inline Col_iterator::Col_iterator(int refer, int i) 
  : Simple_iterator(i), ref(refer) {
} 

inline bool operator == (Col_iterator i1, Col_iterator i2) {
  return i1.iter == i2.iter && i1.ref == i2.ref;
}

inline bool operator != (Col_iterator i1, Col_iterator i2) {
  return !(i1 == i2);
}

inline ostream& operator <<(ostream& out, Col_iterator i) {
  out << "< " << i.ref << ", " << i.iter << " >";
  return out;
}

} // namespace FF

#endif // FF_ITERATOR_INLINES_HPP

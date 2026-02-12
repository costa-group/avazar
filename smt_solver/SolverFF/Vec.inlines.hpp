#ifndef FF_VEC_INLINES_HPP
#define FF_VEC_INLINES_HPP

#include "Vec.defs.hpp"

namespace FF {

template<class T>
inline void Vec<T>::grow_capacity(int min_cap) {

  FF_ASSERT(VEC, cap <= min_cap);
  if (cap == 0)
    cap = (min_cap >= 2) ? min_cap : 2;
  else
    do
      cap = (3*cap + 1) >> 1;
    while (cap < min_cap);

  data = (T*) realloc((void*) data, cap * sizeof(T));
  FF_ASSERT(VEC, data != NULL);
}


template<class T>
inline void Vec<T>::grow_size(int size, const T& pad) {

  FF_ASSERT(VEC, sz <= size);

  int old_cap = cap;
  if (size > cap) {
    grow_capacity(size);

    for (int i = old_cap; i < cap; i++)
      new (&data[i]) T(pad);
  }
  sz = size;
}


template<class T>
inline void Vec<T>::grow_size(int size) {

  FF_ASSERT(VEC, sz <= size);

  int old_cap = cap;
  if (size > cap) {
    grow_capacity(size);
    
    for (int i = old_cap; i < cap; i++)
      new (&data[i]) T();
  }
  sz = size;
}


template<class T>
inline Vec<T>::Vec(void) : data(NULL), sz(0), cap(0) { }


template<class T>
inline Vec<T>::Vec(int size) : data(NULL), sz(0), cap(0) {
  grow_size(size);
}


template<class T>
inline Vec<T>::Vec(int size, const T& pad) : data(NULL), sz(0), cap(0) {
  grow_size(size, pad);
}


template<class T>
inline Vec<T>::Vec(const Vec<T>& v) : data(NULL) , sz(v.sz), cap(0) {

  grow_capacity(sz);

  // Copying 'v'.
  for (int i = 0; i < sz; i++)
    new (&data[i]) T(v[i]);

  // Padding the rest of the vector with the default constructor.
  for (int i = sz; i < cap; i++)
    new (&data[i]) T();
}


template<class T>
inline Vec<T>::~Vec(void) {
  if (data != NULL) {
    for (int i = 0; i < cap; i++)
      data[i].~T();

    cap = 0;
    free((void*) data);
    data = NULL;
    sz = 0;
  }
}


// push could be also implemented using grow_size. However, assuming
// that the default constructor for T is cheaper than a copy
// constructor, the current implementation of push(const T& elem) is
// more efficient than that relying on grow_size. For consistency,
// push(void) is implemented not using grow_size too.
template<class T>
inline void Vec<T>::push(void) {

  if (sz == cap) {
    grow_capacity(sz + 1);

    // All newly allocated values are initialised with the default
    // constructor.
    for (int i = sz; i < cap; i++)
      new(&data[i]) T();
  }
  sz++;
}


template<class T>
inline void Vec<T>::push(const T& elem) {

  if (sz == cap) {
    grow_capacity(sz + 1);
    new(&data[sz]) T(elem);

    // Except for the first, all the newly allocated values are
    // initialised with the default constructor.
    for (int i = sz + 1; i < cap; i++)
      new(&data[i]) T();
  }
  else
    data[sz] = elem;

  sz++;
}


template<class T>
inline int Vec<T>::size(void) const {
  return sz;
}


template<class T>
inline void Vec<T>::grow_to(int size, const T& pad) {

  if (sz < size)
    grow_size(size, pad);
}


template<class T>
inline void Vec<T>::grow_to(int size) {

  if (sz < size)
    grow_size(size);
}


template<class T>
inline void Vec<T>::shrink(int nelems) {

  FF_ASSERT(VEC, nelems >= 0 && nelems <= sz);

  sz -= nelems;
}


template<class T>
inline void Vec<T>::clear(void) {

  sz = 0;
}


template<class T>
inline void Vec<T>::pop(void) {
  FF_ASSERT(VEC, sz > 0);
  sz--;
}


template<class T>
inline const T& Vec<T>::top(void) const {
  FF_ASSERT(VEC, sz > 0); 
  return data[sz - 1];
}


template<class T>
inline T& Vec<T>::top(void) {
  FF_ASSERT(VEC, sz > 0); 
  return data[sz - 1];
}


template<class T>
inline const T& Vec<T>::operator [](int i) const {
  FF_ASSERT(VEC, i >= 0 && i < sz); 
  return data[i];
}


template<class T>
inline T& Vec<T>::operator [](int i) {
  FF_ASSERT(VEC, i >= 0 && i < sz); 
  return data[i];
}


template<class T>
inline void Vec<T>::remove(int i) {
  FF_ASSERT(VEC, i >= 0 && i < sz);
  sz--;
  if (i != sz)
    // Copying value in last cell to cell to be removed.
    data[i] = data[sz];
}


template <class T>
inline bool operator ==(const Vec<T>& v1, const Vec<T>& v2) {
  FF_ASSERT(VEC, v1.sz == v2.sz);

  for (int i = 0; i < v1.sz; ++i)
    if (v1.data[i] != v2.data[i])
      return false;

  return true;
}


template <class T>
inline bool operator !=(const Vec<T>& v1, const Vec<T>& v2) {
  return !(v1 == v2);
}


template <class T>
inline void swap(Vec<T> &x, Vec<T> &y) {
  std::swap(x.data, y.data);
  std::swap(x.sz,   y.sz);
  std::swap(x.cap,  y.cap);
}


template <class T>
inline bool ok(const Vec<T>& v) {
  for (int k = 0; k < v.size(); k++)
    if (v[k] != T(0))
      return false;

  return true;  
}


template <class T>
inline ostream& operator <<(ostream& s, const Vec<T>& x) {
  s << "[ ";
  for (int i = 0; i < x.sz; i++) {
    s << x.data[i];  
    if (i + 1 < x.sz) 
      s << ",";
  }
  s << " ]";

  return s;
}


template <class T>
inline void Vec<T>::operator =(const Vec<T>& v) {
    
  grow_to(v.sz);
  sz = v.sz;
  for (int i = 0; i < sz; ++i)
    data[i] = v.data[i];
}


template <class T>
inline bool Vec<T>::ok(void) {

  if (sz > cap) {
    cout << "Should be sz <= cap" << endl;
    return false;
  }

  if (sz < 0) {
    cout << "sz should be non-negative" << endl;
    return false;
  }

  if (cap < 0) {
    cout << "cap should be non-negative" << endl;
    return false;
  }

  // Class invariant: if data == NULL, then cap == 0.
  if (data == NULL && cap > 0) {
    cout << "If data == NULL, then cap == 0" << endl;
    return false;
  }

  return true;
}


} // namespace FF

#endif // FF_VEC_INLINES_HPP

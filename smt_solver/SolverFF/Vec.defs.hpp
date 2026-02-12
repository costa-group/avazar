#ifndef FF_VEC_DEFS_HPP
#define FF_VEC_DEFS_HPP

#include "Global.hpp"

namespace FF {

template<class T>
class Vec;

template <class T>
bool operator ==(const Vec<T>& v1, const Vec<T>& v2);

template <class T>
bool operator !=(const Vec<T>& v1, const Vec<T>& v2);

template <class T>
ostream& operator <<(ostream &s, const Vec<T>& x);

template <class T>
void swap(Vec<T>& x, Vec<T>& y);

template <class T>
bool ok(const Vec<T>& v); // True if v is all T(0)'s.


//////////////////////
//// CLASS Vec<T> ////
//////////////////////

// Class for dynamic arrays of elements of type T.

template<class T>
class Vec {

public:

  /////////////////////////////////
  // Constructors and destructor //
  /////////////////////////////////

  Vec (void);
  Vec (int size);
  Vec (int size, const T& pad);
  Vec (const Vec<T>& pad);
  ~Vec(void);


  ////////////////////
  // Dynamic sizing //
  ////////////////////

  int  size   (void) const;

  // Do not shrink the vector if size < current size.
  // Only if more memory is needed the default/copy constructors
  // are called. Otherwise reused cells may contain garbage.
  void grow_to(int size);                
  void grow_to(int size, const T& pad);

  void shrink (int nelems);
  void clear  (void);        // Does not release memory.


  /////////////////////            
  // Stack interface //
  /////////////////////

  void push(void);       // No guarante new cell has default value.
  void push(const T& e); // New cell is guaranteed to store e.
  void     pop (void);
  const T& top (void) const;
  T&       top (void);

  /////////////////////
  // Array interface //
  /////////////////////

  const T& operator [](int i) const;
  T&       operator [](int i); 

  // Swaps last cell with i-th cell and then deletes last cell.
  void remove(int i);


  ////////////
  // Others //
  ////////////

  // Output.
  friend ostream& operator << <T>(ostream& s, const Vec<T>& x);

  // Swap method.
  friend void swap<T>(Vec<T> &x, Vec<T> &y);

  // Assignment functions.
  void operator =(const Vec<T> & v);

  // Comparison of vectors componentwise.
  friend bool operator ==<T>(const Vec<T>& v1, const Vec<T>& v2);
  friend bool operator !=<T>(const Vec<T>& v1, const Vec<T>& v2);

  // Debugging.
  bool ok(void);


private:

  T*  data;
  int sz;  // Size of the vector.
  int cap; // Size of the allocated memory (cap >= size).

  // All allocated memory is properly initialised using the
  // constructor of 'T', to avoid calling the constructor/destructor
  // of 'T' too often.

  // Allocates memory for a vector of size at least min_cap,
  // without calling the constructor of 'T'.
  void grow_capacity(int min_cap);

  // Enlarges the vector so that all newly allocated positions are
  // initialised calling the copy constructor with argument 'pad'.
  void grow_size    (int size, const T& pad);

  // Enlarges the vector so that all newly allocated positions are
  // initialised calling the default constructor.
  void grow_size    (int size);

}; // End of class Vec<T>.

} // namespace FF

#endif // FF_VEC_DEFS_HPP

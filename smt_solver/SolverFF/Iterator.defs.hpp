#ifndef FF_ITERATOR_DEFS_HPP
#define FF_ITERATOR_DEFS_HPP

#include "Global.hpp"

namespace FF {

class F_matrix;
class C_matrix;

///////////////////////////////
//// CLASS Simple_iterator ////
///////////////////////////////

// Base class for iterators consisting in a single integer.

class Simple_iterator {
  
public:
    
  explicit Simple_iterator(void); // Creates the iterator pointing nowhere.
  explicit Simple_iterator(int i);
  Simple_iterator(const Simple_iterator& i);
  void operator =(const Simple_iterator& i);    

  friend bool operator ==(Simple_iterator i, Simple_iterator j);
  friend bool operator !=(Simple_iterator i, Simple_iterator j);

  friend ostream& operator <<(ostream& out, Simple_iterator v);

protected:

  int iter;

}; // End of class Simple_iterator.


////////////////////////////////
//// CLASS Complex_iterator ////
////////////////////////////////

// Base class for iterators consisting in pairs of integers.

class Complex_iterator {
  
public:
    
  explicit Complex_iterator(void); // Creates iterator pointing nowhere.
  explicit Complex_iterator(int bs, int off);
  Complex_iterator(const Complex_iterator& i);
  void operator =(const Complex_iterator& i);    

  friend bool operator ==(const Complex_iterator& i, const Complex_iterator& j);
  friend bool operator !=(const Complex_iterator& i, const Complex_iterator& j);

  friend ostream& operator <<(ostream& out, const Complex_iterator& v);

  // Not made private for convenience.
  int base;
  int offset;

}; // End of class Complex_iterator.


/////////////////////////////
//// CLASS Row_iterator /////
/////////////////////////////

// Class for iterating over the entries != 0 of rows.

class Row_iterator : public Simple_iterator {

public:

  Row_iterator(void);
  void next(const F_matrix& m);
  void next(const C_matrix& m);
  
  friend ostream& operator <<(ostream& out, Row_iterator v);

private:

  Row_iterator(int ref, int i);

  int ref;

  friend class F_matrix;
  friend class C_matrix;
  
}; // End of class Row_iterator.


////////////////////////////
//// CLASS Col_iterator ////
////////////////////////////

// Class for iterating over entries != 0 of columns in a group.

class Col_iterator : public Simple_iterator {

public:

  Col_iterator(void);
  void next(const F_matrix& m);
  void next(const C_matrix& m);
  friend bool operator == (Col_iterator i1, Col_iterator i2);
  friend bool operator != (Col_iterator i1, Col_iterator i2);


  friend ostream& operator <<(ostream& out, Col_iterator v);

private:

  Col_iterator(int ref, int i);

  int ref;

  friend class F_matrix;
  friend class C_matrix;

}; // End of class Col_iterator.

} // namespace FF

#endif // FF_ITERATOR_DEFS_HPP

#ifndef FF_BASIS_DEFS_HPP
#define FF_BASIS_DEFS_HPP

#include "Global.hpp"
#include "Vec.defs.hpp"
#include "Int_set.defs.hpp"

namespace FF {

///////////////////////
///// CLASS Basis /////
///////////////////////

class Basis {

public:

  // Creates basis with n_cols columns and with no rows
  // (hence all columns are non-basic by default).
  Basis(int n_cols); 

  // Number of rows.
  int row_dimension() const;

  // Number of columns.
  int col_dimension() const;

  // Makes column c become basic of a new row.
  // Aborts if c was already basic.
  void insert_new_row(int c);

  // Removes last row.
  // Basic column of last row becomes non-basic.
  void remove_last_row();

  // Inserts a new column (non-basic).
  void insert_new_col();

  // Removes last column.
  // Aborts if last column is basic.
  void remove_last_col();

  // ob is the *o*utgoing     *b*asic column.
  // in is the *i*ncoming *n*on-basic column.
  void pivot(int ob, int in);

  // Swaps rows of basic columns c1 and c2.
  // Aborts if c1 or c2 are non-basic.
  void swap(int c1, int c2);

  // If c is basic, returns its row.
  // Otherwise, returns WRONG_INDEX.
  int row(int c) const;

  // Returns the basic column of r-th row.
  int col(int r) const;

  friend ostream& operator<<(ostream& out, const Basis& b);


  /////////////////////////
  //// CLASS Iterator /////
  /////////////////////////
  
  // Class for iterating over basic columns.
  
  class Iterator {
    
  public:
    
    void next(const Basis& b);

    friend bool operator ==(Iterator i, Iterator j);
    friend bool operator !=(Iterator i, Iterator j);
    
  private:
    
    Iterator(Int_set::Iterator);
    
    Int_set::Iterator iter;
    
    friend class Basis;

  }; // End of class Iterator.

  Iterator beg() const; // Returns the first iterator.
  Iterator end() const; // Returns the next to the last valid.

  int col(Iterator i) const;


private:

  // Set of basic columns.
  Int_set basic; 

  // row2col[r] is the basic column of row r.
  Vec<int> row2col;

  // col2row[c] is the row of c is c is basic, WRONG_INDEX otherwise.
  Vec<int> col2row;

}; // End of class Basis.

ostream& operator<<(ostream& out, const Basis& b);

} // namespace FF

#endif // FF_BASIS_DEFS_HPP

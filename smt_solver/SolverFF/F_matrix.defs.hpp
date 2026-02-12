#ifndef FF_F_MATRIX_DEFS_HPP
#define FF_F_MATRIX_DEFS_HPP

#include "Zp.hpp"
#include "Iterator.defs.hpp"
#include "Vec.defs.hpp"


namespace FF {

////////////////////////
//// CLASS F_matrix ////
////////////////////////

// Class for matrix storing simplex tableau.
// F short for "Full", since rows are fully expanded.

class F_matrix {

public:

  F_matrix(int ini_col_dim, int row_capacity);
  F_matrix(const F_matrix& f);

  int row_dimension(void) const;
  int col_dimension(void) const;

  void insert_new_row(void); // Inserts a new empty row.
  void insert_new_col(void); // Inserts a new empty col.

  // No. elements != 0 in row r.
  int row_size(int r) const; 

  // Removes last column to the matrix.
  // Aborts if last column is not empty.
  // Aborts if col dimension == 0.
  void remove_last_col(void);

  // Removes the last row.
  // Aborts if the row is not empty.
  // Aborts if row dimension == 0.
  void remove_last_row(void);

  // Clears the last row.
  // Aborts if last row belongs to IDLE.
  void clear_last_row(void);

  // Inserts entry with value v at column c at last row.
  // Aborts if last row belongs to IDLE.
  // Aborts if v == 0.
  // Aborts if c < 0 or c >= col_dimension.
  void insert_to_last_row(const Zp& v, int c);

  // Access operator.
  const Zp& value(int r, int c) const;

  // Swaps rows r1 and r2.
  void swap_rows(int r1, int r2);

  // Returns the first iterator of row r.
  // Aborts if r < 0 or r >= row_dimension().
  Row_iterator row_beg(int r) const;

  // Returns the next to the last valid iterator of row r.
  // Aborts if r < 0 or r >= row_dimension().
  Row_iterator row_end(int r) const;

  // Returns the coefficient of the entry pointed by i.
  // Aborts if i is not a valid iterator.
  const Zp& value(const Row_iterator& i) const;
  Zp&       value(const Row_iterator& i)      ;

  // Returns the column index of the entry pointed by i.
  // Aborts if i is not a valid iterator.
  int index(const Row_iterator& i) const;

  // Returns the first iterator of column c.
  // Aborts if c < 0 or c >= col_dimension().
  Col_iterator col_beg(int c) const;

  // Returns the first iterator of column c.
  // Aborts if c < 0 or c >= col_dimension().
  Col_iterator col_end(int c) const;

  // Returns the coefficient of the entry pointed by i.
  // Aborts if i is not a valid iterator.
  const Zp& value(const Col_iterator& i) const;

  // Returns the row index of the entry pointed by i.
  // Aborts if i is not a valid iterator.
  int index(const Col_iterator& i) const;

  // Pivots with row r and column c.
  void pivot(int r, int c);

  // Printing.
  friend ostream& operator << (ostream& out, const F_matrix& r);

  // Access operator.
  Zp& value(int r, int c);

  // Row r1 becomes a*r1 + b*r2.
  void add_mul(const Zp& a, int r1, const Zp& b, int r2);
  

private:

  // TYPES
  ////////
  
  struct Pointer {
    int forw;
    int back;

    Pointer(void) { }
  };

  friend ostream& operator <<(ostream& out, Pointer p);

  struct Block {
    Zp coeff;
    Pointer point;

    Block(void) : coeff(0) { }
  };


  // FUNCTIONS
  ////////////

  // Inserts entry with value v at row r and column c.
  // Aborts if value == 0.
  // Aborts if r < 0 or r >= row_dimension.
  // Aborts if c < 0 or c >= col_dimension.
  void insert(const Zp& v, int r, int c);

  // Removes entry at row r and column c.
  // Aborts if value == 0.
  // Aborts if r < 0 or r >= row_dimension.
  // Aborts if c < 0 or c >= col_dimension.
  void remove(int r, int c);

  // Divides all entries in row r by the GCD of its coefficients.
  // Aborts if row is empty.
  // Aborts if r < 0 or r >= row_dimension.
  void simplify(int r);

  void add_row_support(int r, int c); // Adds entry to row support.
  void add_col_support(int r, int c); // Adds entry to col support.

  void remove_row_support(int r, int c); // Removes entry from row support.
  void remove_col_support(int r, int c); // Removes entry from col support.

  // No. elements != 0 in column c and active rows.
  int col_size(int c) const; 


  // PRIVATE FIELDS
  /////////////////
  
  // Both row and column supports are implemented as circular
  // doubly-linked lists with sentinels.

  // Coefficients of matrix are stored together with row supports for
  // efficiency, since while pivoting matrix is scanned by rows.

  // The 0-th variable is a dummy variable for which coefficients in
  // all rows are 0. SO NOTHING ABOUT THE 0-th VARIABLE IS EVER ASKED.
  // This allows using 0 for sentinels in implementation of rows.

  // The 0-th row is a dummy row for which coefficients in all columns
  // are 0.  SO NOTHING ABOUT THE 0-th ROW IS EVER ASKED. This allows
  // using 0 for sentinels in implementation of columns.

  // row[r] (1 <= r < row_dim) is the r-th row, represented as a
  // vector of size col_dim of pairs (coeff, point), where coeff
  // represents coefficient and point points to previous and next in
  // support. First entry of row r is row[r][0], and following
  // pointers rest of support can be iterated over.
  Vec< Vec< Block > > row;

  // col[c] (1 <= c < col_dim) is the c-th column (without inactive
  // entries), represented as a vector of size row_dim of pointers
  // pointing to previous and next entry in support. First entry of
  // col c is col[c][0], and following pointers rest of support
  // can be iterated over.
  Vec< Vec<Pointer> > col;

  // row_sz[r] is no. of entries in row r with non-null coefficient.
  Vec<int> row_sz;

  int col_dim;
  
  // For example, the matrix

  //    0  1  2  3  4
  //   ---------------
  // 0| 0  0  0  0  0   <-- dummy row
  // 1| 0  2  0 -1  0   <-- ACTIVE
  // 2| 0  0  3 -3  0   <-- inactive
  // 3| 0  1 -2  1  4   <-- ACTIVE
  //    ^
  //    dummy column


  // could be stored as (? means the value does not care)


  //                 0        1         2         3        4
  //            -------------------------------------------------     
  // row: 0 --> [ [?|?|?]  [?|?|?]  [ ?|?|?]  [ ?|?|?]  [?|?|?] ]
  //      1 --> [ [?|1|3]  [2|3|0]  [ 0|?|?]  [-1|0|1]  [0|?|?] ]
  //      2 --> [ [?|3|2]  [0|?|?]  [ 3|0|3]  [-3|2|0]  [0|?|?] ]
  //      3 --> [ [?|1|4]  [1|2|0]  [-2|3|1]  [ 1|4|2]  [4|0|3] ]
  //                 ^
  //                 sentinel


  // col:     [0]       [1]       [2]       [3]      [4]
  //           |         |         |         |        | 
  //           V         V         V         V        V
  //  0 |    [?|?]     [3|1]     [3|3]     [1|3]    [3|3]
  //  1 |    [?|?]     [0|3]     [?|?]     [3|0]    [?|?]
  //  2 |    [?|?]     [?|?]     [?|?]     [?|?]    [?|?]
  //  3 |    [?|?]     [1|0]     [0|0]     [0|1]    [0|0]

  friend class Row_iterator;
  friend class Col_iterator;

}; // End of class F_matrix.

ostream& operator << (ostream& out, const F_matrix& r);

} // namespace FF.

#endif // FF_F_MATRIX_DEFS_HPP

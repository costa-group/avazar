#ifndef FF_C_MATRIX_DEFS_HPP
#define FF_C_MATRIX_DEFS_HPP

#include "Zp.hpp"
#include "Iterator.defs.hpp"
#include "Vec.defs.hpp"
#include "Int_set.defs.hpp"


namespace FF {

////////////////////////
//// CLASS C_matrix ////
////////////////////////

// Class for matrix storing simplex tableau.
// C short for "Compressed", since rows are compressed.

class C_matrix {

public:

  C_matrix(int ini_col_dim);
  C_matrix(const C_matrix& m);

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
  // Aborts if r1 or r2 belong to IDLE.
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
  friend ostream& operator <<(ostream& out, const C_matrix& m);

  // Row r1 becomes a*r1 + b*r2.
  void add_mul(const Zp& a, int r1, const Zp& b, int r2);
  

private:

  // TYPES
  ////////

  typedef Complex_iterator Pair;

  struct Block {
    Zp      val;
    int     idx;
    int     arw;

    Block(void) : arw(WRONG_INDEX) { }
    Block(Zp v, int i, int a) : val(v), idx(i), arw(a)  { }
  };

  friend ostream& operator <<(ostream& out, const C_matrix::Block& b);

  // FUNCTIONS
  ////////////

  // Inserts entry with coefficient value at row r and column c.
  // Aborts if value == 0.
  // Aborts if r < 0 or r >= row_dimension.
  // Aborts if c < 0 or c >= col_dimension.
  void insert(const Zp& value, int r, int c);

  // Removes k-th entry at row r.
  // Aborts if r < 0 or r >= row_dimension.
  void remove(int k, int r);

  // Divides all entries in row r by the GCD of its coefficients.
  // Aborts if row is empty.
  // Aborts if r < 0 or r >= row_dimension.
  void simplify(int r);

  // No. elements != 0 in column c and active rows.
  int col_size(int c) const; 


  // PRIVATE FIELDS
  /////////////////

  // Array of rows, for which only non-null entries are stored.
  Vec< Vec<Block> > matrix;

  // col_sup[j] stores those
  // entries of the j-th column with rows in group ACTIVE:
  // for the k-th non-null entry,
  // * col_sup[j][k].base   is row r in m of entry;
  // * col_sup[j][k].offset is position in val[r] of entry.
  Vec< Vec<Pair> >  col_sup;

  // Working vector.
  Vec<Zp> w;

  // Constant number zero.
  Zp ZERO;

  // A C_matrix stores its coefficients by rows: for any 0 <= i <
  // row_dimension(), val[i], col_index[i] and col_arrow[i] is the
  // i-th row of the matrix: val[i] is the coefficient, col_index[i]
  // is the column index, and col_arrow[i] is the index k such that
  // col_sup[col_index[i]][k] corresponds to this entry, if
  // the row belongs to group ACTIVE.

  // For any 0 <= j < col_dimension(), col_sup[j] stores those
  // entries of the j-th column with rows in ACTIVE group:
  // the k-th entry of col_sup[j] consists of two numbers base and
  // offset: base is the row of the entry (which is active), and
  // offset is the index corresponding to this entry in val[base].

  // Data for column iterating is only stored for active groups.

  // For example, the matrix
  //    0  1  2  3
  //   ----------
  // 0| 3  0  2  0
  // 1| 0  1 -1  0
  // 2| 4  0  0  0
  // 3| 0  0  0 -1

  // would be stored as

  //      val     col_index   col_arrow
  //    =======   =========   =========
  // 0 |  2  3      2  0        0  0
  // 1 |  1 -1      1  2        0  1
  // 2 |  4         0           1
  // 3 | -1         3           0
  //
  //                                  (all rows of group ACTIVE)
  // col_sup     [0]  [1]  [2] [3]
  // ==========   |    |    |   |
  //              V    V    V   V
  //      [0]    0|1  1|0  0|0 3|0
  //      [1]    2|0       1|1
  //

  friend class Row_iterator;
  friend class Col_iterator;

}; // End of class C_matrix.

ostream& operator << (ostream& out, const C_matrix& r);

} // namespace FF

#endif // FF_C_MATRIX_DEFS_HPP

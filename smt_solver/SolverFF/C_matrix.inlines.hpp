#ifndef FF_C_MATRIX_INLINES_HPP
#define FF_C_MATRIX_INLINES_HPP

#include "C_matrix.defs.hpp"
#include "Iterator.inlines.hpp"
#include "Vec.inlines.hpp"
#include "Int_set.inlines.hpp"

namespace FF {

inline C_matrix::C_matrix(int ini_col_dim) :
  w(ini_col_dim, Zp(0)), ZERO(Zp(0)) {
  
  col_sup.grow_to(ini_col_dim);
  insert_new_row();
}

inline C_matrix::C_matrix(const C_matrix& m) :
  matrix(m.matrix),
  w(m.w) {

  col_sup = m.col_sup;
}

inline int C_matrix::row_dimension(void) const {
  return matrix.size();
}

inline int C_matrix::col_dimension(void) const {
  return col_sup.size();
}

inline void C_matrix::insert_new_row(void) {

  matrix.push();

  FF_ASSERT(C_MATRIX, matrix.top().size() == 0);
}

inline void C_matrix::insert_new_col(void) {

  col_sup.push();
  FF_ASSERT(C_MATRIX, col_sup.top().size() == 0);
  
  w.push(Zp(0));
}

inline void C_matrix::remove_last_row(void) {
  
  FF_ASSERT(C_MATRIX, row_dimension() > 0);
  FF_ASSERT(C_MATRIX, matrix.top().size() == 0);
  matrix.pop();
}

inline void C_matrix::remove_last_col(void) {
  FF_ASSERT(C_MATRIX, col_dimension() > 0);

  FF_ASSERT(C_MATRIX, col_sup.top().size() == 0);
  col_sup.pop();
  w.pop();
}

inline void C_matrix::insert(const Zp& value, int r, int c) {
  FF_ASSERT(C_MATRIX, 0 <= r && r < row_dimension());
  FF_ASSERT(C_MATRIX, 0 <= c && c < col_dimension());
  FF_ASSERT(C_MATRIX, value != 0);

  int k = matrix[r].size();
  matrix[r].push( Block(value, c, col_sup[c].size()) );
  col_sup[c].push(Pair(r, k));
}

inline ostream& operator << (ostream& out, const C_matrix::Block& b) {
  out << "[" 
      << "val = " << b.val << ", "
      << "idx = " << b.idx << ", "
      << "arw = " << b.arw 
      << "]";

  return out;
}


inline const Zp& C_matrix::value(int r, int c) const {
  for (Row_iterator k = row_beg(r), ke = row_end(r); 
       k != ke; k.next(*this))
    if (index(k) == c)
      return value(k);
  return ZERO;
}

inline void C_matrix::insert_to_last_row(const Zp& value, int c) {
  insert(value, row_dimension() - 1, c);
}


inline int C_matrix::row_size(int r) const {
  FF_ASSERT(C_MATRIX, 0 <= r && r < row_dimension());
  return matrix[r].size();
}


inline int C_matrix::col_size(int c) const {
  FF_ASSERT(C_MATRIX, 0 <= c && c < col_dimension());
  return col_sup[c].size();
}


inline Row_iterator
C_matrix::row_beg(int r) const {
  FF_ASSERT(C_MATRIX, r >= 0 && r < row_dimension());
  return Row_iterator(r, matrix[r].size() - 1);
}


inline Row_iterator
C_matrix::row_end(int r) const {
  FF_ASSERT(C_MATRIX, r >= 0 && r < row_dimension());
  return Row_iterator(r, -1);
}


inline const Zp&
C_matrix::value(const Row_iterator& i) const {
  return matrix[i.ref][i.iter].val;
}


inline Zp&
C_matrix::value(const Row_iterator& i) {
  return matrix[i.ref][i.iter].val;
}


inline int
C_matrix::index(const Row_iterator& i) const {
  return matrix[i.ref][i.iter].idx;
}


inline Col_iterator
C_matrix::col_beg(int c) const {
  FF_ASSERT(C_MATRIX, c >= 0 && c < col_dimension());
  return Col_iterator(c, col_sup[c].size() - 1);
}


inline Col_iterator
C_matrix::col_end(int c) const {
  FF_ASSERT(C_MATRIX, c >= 0 && c < col_dimension());
  return Col_iterator(c, -1);
}


inline const Zp&
C_matrix::value(const Col_iterator& i) const {
  const Pair& p = col_sup[i.ref][i.iter];
  return matrix[p.base][p.offset].val;
}


inline int
C_matrix::index(const Col_iterator& i) const {
  return col_sup[i.ref][i.iter].base;
}


inline void Row_iterator::next(const C_matrix& m) {
  iter--;
}


inline void Col_iterator::next(const C_matrix& m) {
  iter--;
}


} // namespace FF

#endif // FF_C_MATRIX_INLINES_HPP

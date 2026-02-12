#ifndef FF_F_MATRIX_INLINES_HPP
#define FF_F_MATRIX_INLINES_HPP

#include "Iterator.inlines.hpp"
#include "Vec.inlines.hpp"
#include "F_matrix.defs.hpp"

namespace FF {

inline F_matrix::F_matrix(const F_matrix& m) :
  row(m.row),
  col(m.col),
  row_sz(m.row_sz),
  col_dim(m.col_dim) {
}

inline void F_matrix::add_row_support(int r, int c) {
  int next = row[r][0].point.forw;
  row[r][c].point.forw = next;
  row[r][c].point.back = 0;
  row[r][0]   .point.forw = c;
  row[r][next].point.back = c;
}

inline void F_matrix::add_col_support(int r, int c) {
  int next = col[c][0].forw;
  col[c][r].forw = next;
  col[c][r].back = 0;
  col[c][0]   .forw = r;
  col[c][next].back = r;
}

inline void F_matrix::remove_row_support(int r, int c) {
  int next = row[r][c].point.forw;
  int prev = row[r][c].point.back;
  row[r][prev].point.forw = next;
  row[r][next].point.back = prev;
}

inline void F_matrix::remove_col_support(int r, int c) {
  int next = col[c][r].forw;
  int prev = col[c][r].back;
  col[c][prev].forw = next;
  col[c][next].back = prev;
}

inline int F_matrix::row_dimension(void) const {
  return row_sz.size();
}

inline int F_matrix::col_dimension(void) const {
  return col_dim;
}

inline void F_matrix::remove_last_row(void) {
  FF_ASSERT(F_MATRIX, row_size(row_dimension() - 1) == 0);
  row_sz.pop();
}

inline void F_matrix::remove_last_col(void) {
  FF_ASSERT(F_MATRIX, col_size(col_dimension() - 1) == 0);
  --col_dim;
}

inline void F_matrix::insert_to_last_row(const Zp& v, int c) {
  FF_ASSERT(F_MATRIX, 1 <= c && c < col_dimension());
  insert(v, row_dimension() - 1, c);
}

inline const Zp& F_matrix::value(int r, int c) const {
  FF_ASSERT(F_MATRIX, 1 <= r && r < row_dimension());
  FF_ASSERT(F_MATRIX, 1 <= c && c < col_dimension());

  return row[r][c].coeff;
}

inline Zp& F_matrix::value(int r, int c) {
  FF_ASSERT(F_MATRIX, 1 <= r && r < row_dimension());
  FF_ASSERT(F_MATRIX, 1 <= c && c < col_dimension());

  return row[r][c].coeff;
}

inline void F_matrix::insert(const Zp& v, int r, int c) {

  FF_ASSERT(F_MATRIX, v != 0);
  FF_ASSERT(F_MATRIX, value(r, c) == 0);
  FF_ASSERT(F_MATRIX, 1 <= r && r < row_dimension());
  FF_ASSERT(F_MATRIX, 1 <= c && c < col_dimension());

  row[r][c].coeff = v;
  ++row_sz[r];
  add_row_support(r, c);
  add_col_support(r, c);
}


inline Row_iterator
F_matrix::row_beg(int r) const {
  FF_ASSERT(F_MATRIX, r >= 1 && r < row_dimension());
  return Row_iterator(r, row[r][0].point.back);
}

inline Row_iterator
F_matrix::row_end(int r) const {
  FF_ASSERT(F_MATRIX, r >= 1 && r < row_dimension());
  return Row_iterator(r, 0);
}

inline const Zp&
F_matrix::value(const Row_iterator& i) const {
  int r = i.ref;
  int c = i.iter;
  FF_ASSERT(F_MATRIX, row[r][c].coeff != 0);
  return row[r][c].coeff;
}

inline Zp&
F_matrix::value(const Row_iterator& i) {
  int r = i.ref;
  int c = i.iter;
  FF_ASSERT(F_MATRIX, row[r][c].coeff != 0);
  return row[r][c].coeff;
}

inline int
F_matrix::index(const Row_iterator& i) const {
  return i.iter;
}

inline Col_iterator
F_matrix::col_beg(int c) const {
  FF_ASSERT(F_MATRIX, c >= 1 && c < col_dimension());
  return Col_iterator( c, col[c][0].back);
}

inline Col_iterator
F_matrix::col_end(int c) const {
  FF_ASSERT(F_MATRIX, c >= 1 && c < col_dimension());
  return Col_iterator( c, 0);
}

inline const Zp&
F_matrix::value(const Col_iterator& i) const {
  int c = i.ref;
  int r = i.iter;
  FF_ASSERT(F_MATRIX, row[r][c].coeff != 0);
  return row[r][c].coeff;
}

inline int
F_matrix::index(const Col_iterator& i) const {
  return i.iter;
}

inline void F_matrix::remove(int r, int c) {

  FF_ASSERT(F_MATRIX, value(r, c) == 0);
  FF_ASSERT(F_MATRIX, 1 <= r && r < row_dimension());
  FF_ASSERT(F_MATRIX, 1 <= c && c < col_dimension());

  --row_sz[r];
  remove_row_support(r, c);
  remove_col_support(r, c);
}

inline void Row_iterator::next(const F_matrix& m) {
  iter = m.row[ref][iter].point.back;
}

inline void Col_iterator::next(const F_matrix& m) {
  iter = m.col[ref][iter].back;
}

} // namespace FF

#endif // FF_F_MATRIX_INLINES_HPP

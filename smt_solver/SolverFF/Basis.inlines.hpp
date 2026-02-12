#ifndef FF_BASIS_INLINES_HPP
#define FF_BASIS_INLINES_HPP

#include "Global.hpp"
#include "Vec.inlines.hpp"
#include "Int_set.inlines.hpp"
#include "Basis.defs.hpp"

namespace FF {


inline Basis::Basis(int n_cols) 
  : basic(n_cols), col2row(n_cols, WRONG_INDEX) {

  FF_ASSERT(BASIS, n_cols > 0);
}


inline int Basis::row_dimension() const {
  return row2col.size();
}


inline int Basis::col_dimension() const {
  return col2row.size();
}


inline void Basis::insert_new_row(int c) {
  FF_ASSERT(BASIS, 0 <= c && c < col_dimension());
  FF_ASSERT(BASIS, row(c) == WRONG_INDEX);

  int r = row2col.size();
  col2row[c] = r;
  row2col.push(c);
  basic.insert(c);
}


inline void Basis::remove_last_row() {
  int c = col( row2col.size() - 1 );
  basic.remove(c);
  row2col.pop();
  col2row[c] = WRONG_INDEX;
}


inline void Basis::insert_new_col() {
  
  basic.enlarge_range(1);
  col2row.push(WRONG_INDEX);
}


inline void Basis::remove_last_col() {
  FF_ASSERT(BASIS, row( col2row.size() - 1 ) == WRONG_INDEX);

  col2row.pop();
  basic.reduce_range(1);
}


inline void Basis::pivot(int ob, int in) {
  FF_ASSERT(BASIS, row(ob) != WRONG_INDEX);
  FF_ASSERT(BASIS, row(in) == WRONG_INDEX);

  int r = row(ob);
  basic.remove(ob);
  basic.insert(in);
  col2row[in] = r;
  col2row[ob] = WRONG_INDEX;
  row2col[r] = in;
}


inline void Basis::swap(int c1, int c2) {

  FF_ASSERT(BASIS, row(c1) != WRONG_INDEX);
  FF_ASSERT(BASIS, row(c2) != WRONG_INDEX);

  int r1 = row(c1);
  int r2 = row(c2);

  std::swap(col2row[c1], col2row[c2]);
  row2col[r1] = c2;
  row2col[r2] = c1;
}


inline int Basis::row(int c) const {
  FF_ASSERT(BASIS, 0 <= c && c < col_dimension());
  return col2row[c];
}


inline int Basis::col(int r) const {
  FF_ASSERT(BASIS, 0 <= r && r < row_dimension());
  return row2col[r];
}


inline Basis::Iterator::Iterator(Int_set::Iterator i) 
  : iter(i) {
} 


inline Basis::Iterator
Basis::beg() const {
  return Iterator(basic.beg());
}


inline Basis::Iterator
Basis::end() const {
  return Iterator(basic.end());
}


inline int
Basis::col(Iterator i) const {
  return basic.value(i.iter);
}


inline void Basis::Iterator::next(const Basis& b) {
  iter.next(b.basic);
}


inline bool 
operator ==(Basis::Iterator i, Basis::Iterator j) {
  return (i.iter == j.iter);
}


inline bool
operator !=(Basis::Iterator i, Basis::Iterator j) {
  return !(i == j);
}


} // namespace FF

#endif // FF_BASIS_INLINES_HPP

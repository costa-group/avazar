#include "F_matrix.inlines.hpp"

using namespace FF;


FF::F_matrix::F_matrix(int ini_col_dim, int row_capacity) 
  : row(row_capacity), 
    col(ini_col_dim), 
    row_sz(1), // Dummy row.
    col_dim(ini_col_dim) {

  FF_ASSERT(F_MATRIX, ini_col_dim >= 1);  

  for (int i = 0; i < row.size(); i++)
    row[i].grow_to( col.size() );

  for (int j = 0; j < col.size(); j++)
    col[j].grow_to( row.size() );

  for (int i = 1; i < row.size(); i++) // Omitting dummy row.
    row[i][0].point.forw = row[i][0].point.back = 0;

  for (int j = 1; j < col.size(); j++) // Omitting dummy col.
    col[j][0].forw = col[j][0].back = 0;
}


void FF::F_matrix::insert_new_row(void) {

  if (row_sz.size() == row.size()) {
    row.push();
    row.top().grow_to( col.size() );
    row.top()[0].point.forw = row.top()[0].point.back = 0;

    for (int j = 0; j < col.size(); j++)
      col[j].push();
  }
  row_sz.push(0);
}


void FF::F_matrix::insert_new_col(void) {

  if (col_dim == col.size()) {
    col.push();
    col.top().grow_to( row.size() );
    col.top()[0].forw = col.top()[0].back = 0;

    for (int i = 0; i < row.size(); i++)
      row[i].push();
  }
  ++col_dim;
}


int FF::F_matrix::row_size(int r) const {
  
  FF_ASSERT(F_MATRIX, 1 <= r && r < row_dimension());
  return row_sz[r];
}


int FF::F_matrix::col_size(int c) const {

  FF_ASSERT(F_MATRIX, 1 <= c && c < col_dimension());

  int sz = 0;
  for (int j = col[c][0].forw; j != 0; j = col[c][j].forw)
    ++sz;
  return sz;
}


void FF::F_matrix::clear_last_row(void) {

  int r = row_dimension() - 1;
  for (int c = row[r][0].point.forw; c != 0; 
       c = row[r][c].point.forw) {
    remove_col_support(r, c);
    row[r][c].coeff = Zp(0);
  }

  row[r][0].point.forw = row[r][0].point.back = 0;
  row_sz[r] = 0;
}


ostream& FF::operator <<(ostream& out, const F_matrix& m) {

  for (int r = 1; r < m.row_dimension(); ++r) {
    for (int c = 1; c < m.col_dimension(); ++c) {
      out << "\t" << m.value(r, c);
    }
    out << endl;
  }
  return out;
}


void FF::F_matrix::simplify(int r) {

  Row_iterator k   = row_beg(r);
  Row_iterator end = row_end(r);

  FF_ASSERT(F_MATRIX, k != end);

  // Computing gcd of coefficients.
  Zp gcd;
  gcd = value(k);
  k.next(*this);
  while (k != end && gcd != 1) {
    gcd_assign(gcd, value(k), gcd);
    k.next(*this);
  }
  // Dividing all coefficients into gcd.
  if (gcd != 1)
    for (Row_iterator i = row_beg(r), end = row_end(r);
	 i != end; i.next(*this))
      value(i) /= gcd;
}


void F_matrix::
add_mul(const Zp& a0, int r1, const Zp& b0, int r2) {

  Zp tmp, a, b;

  if (a0 == -1 || (b0 == -1 && a0 != 1)) {
    neg_assign(a, a0);
    neg_assign(b, b0);
  }
  else {
    a = a0;
    b = b0;
  }

  FF_ASSERT(F_MATRIX, a != 0);
  FF_ASSERT(F_MATRIX, b != 0);
  FF_ASSERT(F_MATRIX, 0 <= r1 && r1 < row_dimension());
  FF_ASSERT(F_MATRIX, 0 <= r2 && r2 < row_dimension());

  // Assigning r1 := a * r1.
  if (a != 1)
    for (Row_iterator i = row_beg(r1), end = row_end(r1); 
	 i != end; i.next(*this))
      value(i) *= a;
  
  // Only need to change non-null entries in r2.
  if (b == 1) {
    for (Row_iterator i = row_beg(r2), end = row_end(r2); 
	 i != end; i.next(*this)) {
      int c = index(i);
      tmp = value(r2, c);
      if (value(r1, c) != 0) {
	value(r1, c) += tmp;
	if (value(r1, c) == 0)
	  remove(r1, c);
      }
      else
	insert(tmp, r1, c);
    }
  }
  else
    for (Row_iterator i = row_beg(r2), end = row_end(r2); 
	 i != end; i.next(*this)) {
      int c = index(i);
      tmp = value(r2, c);
      tmp *= b;
      if (value(r1, c) != 0) {
	value(r1, c) += tmp;
	if (value(r1, c) == 0)
	  remove(r1, c);
      }
      else
	insert(tmp, r1, c);
    }
}


void F_matrix::pivot(int r, int c) {

  FF_ASSERT(F_MATRIX, 1 <= r && r < row_dimension());
  FF_ASSERT(F_MATRIX, 1 <= c && c < col_dimension());
  FF_ASSERT(F_MATRIX, value(r, c) != 0);

  Zp tmp, tmp2, gcd;

  while (col[c][0].forw != col[c][0].back) { // Column size is > 1.

    // Looking for another row to apply linear combination.
    Col_iterator k = col_beg(c);
    if (index(k) == r)
      k.next(*this);
    int r2 = index(k);
    FF_ASSERT(F_MATRIX, r2 != r);

    // Computing coefficients of rows for the cancellation.
    neg_assign(tmp, value(k));
    tmp2 = value(r, c);
    gcd_assign(gcd, tmp, tmp2);
    if (gcd != 1) {
      tmp  /= gcd;
      tmp2 /= gcd;
    }

    // Applying the linear combination and simplifying.
    add_mul(tmp2, r2, tmp, r);
    simplify(r2);
  }
}


void F_matrix::swap_rows(int r1, int r2) {

  for (int c = row[r1][0].point.forw; c != 0; 
       c = row[r1][c].point.forw)
    if (value(r2, c) == 0) {
      remove_col_support(r1, c);
      add_col_support   (r2, c);
    }

  for (int c = row[r2][0].point.forw; c != 0; 
       c = row[r2][c].point.forw)
    if (value(r1, c) == 0) {
      remove_col_support(r2, c);
      add_col_support   (r1, c);
    }

  swap(row[r1], row[r2]);

  int tmp = row_sz[r1];
  row_sz[r1] = row_sz[r2];
  row_sz[r2] = tmp;
}

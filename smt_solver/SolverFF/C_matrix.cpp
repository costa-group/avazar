#include "C_matrix.inlines.hpp"

using namespace FF;

void C_matrix::remove(int k, int r) {

  int c = matrix[r][k].idx;
  if (k != matrix[r].size() - 1) {  // Not last in row.
    int cit = matrix[r].top().idx;
    int cat = matrix[r].top().arw;
    FF_ASSERT(C_MATRIX, col_sup[cit][cat].base   == r);
    FF_ASSERT(C_MATRIX, col_sup[cit][cat].offset == matrix[r].size() - 1);
    col_sup[cit][cat].offset = k;
  }

  int l = matrix[r][k].arw;
  if (l == col_sup[c].size() - 1)   // Last in col.
    col_sup[c].pop();
  else {                            // Not last in col.
    Pair& p = col_sup[c].top();
    FF_ASSERT(C_MATRIX, matrix[p.base][p.offset].arw == col_sup[c].size() - 1);
    matrix[p.base][p.offset].arw = l;
    col_sup[c].remove(l);
  }
  matrix[r].remove(k);
}


void C_matrix::clear_last_row(void) {

  int r = row_dimension() - 1;
  
  for (int k = 0; k < matrix[r].size(); k++) {

    // Adjusting row pointers in col_sup.
    int c = matrix[r][k].idx;
    int l = matrix[r][k].arw;
    if (l == col_sup[c].size() - 1)
      col_sup[c].pop();
    else {
      Pair& p = col_sup[c].top();
      FF_ASSERT(C_MATRIX, matrix[p.base][p.offset].arw == col_sup[c].size() - 1);
      FF_ASSERT(C_MATRIX, matrix[p.base][p.offset].idx == c);
      matrix[p.base][p.offset].arw = l;
      col_sup[c].remove(l);
    }
  }
  matrix[r].clear();
}


void C_matrix::
add_mul(const Zp& a0, int r1, const Zp& b0, int r2) {

  FF_ASSERT(C_MATRIX, a0 != 0);
  FF_ASSERT(C_MATRIX, b0 != 0);
  FF_ASSERT(C_MATRIX, 0 <= r1 && r1 < row_dimension());
  FF_ASSERT(C_MATRIX, 0 <= r2 && r2 < row_dimension());

  Zp tmp;
  Zp a;
  Zp b;

  if (a0 == -1 || (b0 == -1 && a0 != 1)) {
    neg_assign(a, a0);
    neg_assign(b, b0);
  }
  else {
    a = a0;
    b = b0;
  }

#if FF_DEBUG 
  // Storing rows in full vectors to make sure operation is ok.
  Vec<Zp> v1(col_dimension(), Zp(0));
  Vec<Zp> v2(col_dimension(), Zp(0));
  Vec<Zp> v3(col_dimension(), Zp(0));

  for (int k = 0; k < matrix[r1].size(); k++)
    v1[ matrix[r1][k].idx ] = matrix[r1][k].val;

  for (int k = 0; k < matrix[r2].size(); k++)
    v2[ matrix[r2][k].idx ] = matrix[r2][k].val;

  for (int m = 0; m < col_dimension(); m++) {
    v3[m] += v1[m];
    v3[m] *= a;
    Zp aux = v2[m];
    aux *= b;
    v3[m] += aux;
  }
#endif // FF_DEBUG

  int sz = matrix[r1].size();
  if (a == 1) {
    for (int k = 0; k < sz; k++) {
      int idx = matrix[r1][k].idx;
      w[idx]  = matrix[r1][k].val;
    }
  }
  else {
    for (int k = 0; k < sz; k++) {
      int idx = matrix[r1][k].idx;
      w[idx]  = matrix[r1][k].val;
      w[idx] *= a;
    }
  }

  if (b == 1) {
    for (int k = 0; k < matrix[r2].size(); k++) {
      int c = matrix[r2][k].idx;
      if (w[c] == 0)
	insert(matrix[r2][k].val, r1, c);
      else 
	w[c] += matrix[r2][k].val;
    }
  }
  else {
    for (int k = 0; k < matrix[r2].size(); k++) {
      tmp = matrix[r2][k].val;
      tmp *= b;
      int c = matrix[r2][k].idx;
      if (w[c] == 0)
	insert(tmp, r1, c);
      else 
	w[c] += tmp;
    }
  }

  for (int k = sz - 1; k >= 0; k--) {
    int c = matrix[r1][k].idx;
    if (w[c] == 0)
      remove(k, r1);
    else {
      matrix[r1][k].val = w[c];
      w[c] = Zp(0);
    }
  }

#if FF_DEBUG
  // Checking operation is ok.
  Vec<Zp> v4(col_dimension(), Zp(0));

  for (int k = 0; k < matrix[r1].size(); k++)
    v4[ matrix[r1][k].idx ] = matrix[r1][k].val;

  for (int m = 0; m < col_dimension(); m++)
    FF_ASSERT(C_MATRIX, v4[m] == v3[m]);

#endif // FF_DEBUG
}


void C_matrix::pivot(int r, int c) {

  
  Zp tmp;
  Zp tmp2;

  tmp2 = value(r, c);

  FF_ASSERT(C_MATRIX, tmp2 != 0);

  while (col_size(c) > 1) {
    Col_iterator k = col_beg(c);
    if (index(k) == r)
      k.next(*this);
    int r2 = index(k);
    FF_ASSERT(C_MATRIX, r2 != r);
    neg_assign(tmp, value(k));
    add_mul(tmp2, r2, tmp, r);
    simplify(r2);
  }
}


void C_matrix::simplify(int r) {

  Row_iterator k   = row_beg(r);
  Row_iterator end = row_end(r);

  FF_ASSERT(C_MATRIX, k != end);

  // Computing gcd of coefficients.
  Zp gcd;
  gcd = value(k);
  k.next(*this);
  while (k != end && gcd != Zp(1)) {
    gcd_assign(gcd, value(k), gcd);
    k.next(*this);
  }
  // Dividing all coefficients into gcd.
  if (gcd != Zp(1))
    for (Row_iterator k = row_beg(r), end = row_end(r);
	 k != end; k.next(*this))
      value(k) /= gcd;    
}


void C_matrix::swap_rows(int r1, int r2) {
  FF_ASSERT(C_MATRIX, 0 <= r1 && r1 < row_dimension());
  FF_ASSERT(C_MATRIX, 0 <= r2 && r2 < row_dimension());
  
  if (r1 == r2)
    return;

  // Updating the base field in col_sup and look_up_table.
  for (int k = 0; k < matrix[r1].size(); k++) {
    Pair& p = col_sup[ matrix[r1][k].idx ][ matrix[r1][k].arw ];
    FF_ASSERT(C_MATRIX, p.base == r1);
    p.base = r2;
  }
  for (int k = 0; k < matrix[r2].size(); k++) {
    Pair& p = col_sup[ matrix[r2][k].idx ][ matrix[r2][k].arw ];
    FF_ASSERT(C_MATRIX, p.base == r2);
    p.base = r1;
  }
  swap(matrix[r1], matrix[r2]);
}


ostream& FF::operator <<(ostream& out, const C_matrix& m) {
  for (int r = 1; r < m.row_dimension(); ++r) {
    for (int c = 1; c < m.col_dimension(); ++c) {
      out << "\t" << m.value(r, c);
    }
    out << endl;
  }
  return out;
}


#if FF_PROFILE

FF::C_matrix::Stats::Stats(void) :
  n_add_muls(0) {
}

#endif // FF_PROFILE

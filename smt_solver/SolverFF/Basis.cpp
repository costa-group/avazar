#include "Basis.inlines.hpp"

using namespace FF;

ostream& FF::operator<<(ostream& out, const Basis& b) {

  out << "ROW => COL" << endl;
  for (int r = 0; r < b.row_dimension(); r++)
    out   << "Row " << r             << "\t==>\t" 
	  << "Col " << b.col(r)      << endl;
  out << endl;

  out << "COL => ROW" << endl;
  for (int c = 0; c < b.col_dimension(); c++)
    if (b.row(c) != WRONG_INDEX)
      out << "Col " << c             << "\t==>\t" 
	  << "Row " << b.row(c)      << "\t" << endl;
    else 
      out << "Col " << c             << "\t==>\t" 
	  << "."                     << endl;

  out << endl;

  return out;
}

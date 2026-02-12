#ifndef FF_INT_SET_DEFS_HPP
#define FF_INT_SET_DEFS_HPP

#include "Global.hpp"
#include "Vec.defs.hpp"

namespace FF {

///////////////////////
//// CLASS Int_set ////
///////////////////////

// Class for subsets of { 0, ..., top - 1 }.
// top can be dynamically changed.

class Int_set {

public:

  class Iterator;

  Int_set();               // Creates empty set. Initially top == 0.
  Int_set(int t);          // Creates empty set. Initially top == t.
  Int_set(const Int_set& s);
  void operator =(Int_set& s);

  // Increases top by d.
  void enlarge_range(int d);

  // Decreases top by d.
  void reduce_range(int d);

  // Returns the (strict) upper bound of the range of the set.
  int top() const;

  // Inserts x to the set.
  // Aborts if x is out of range, or if x is already in the set.
  void insert(int x);

  // Removes x from the set.
  // Aborts if x is not in the set.
  void remove(int x);

  // Empties the set.
  void clear();

  bool contains(int x) const; // Aborts if x is out of range.
  bool is_empty()      const;
  int  size    ()      const;

  friend ostream& operator<<(ostream& out, const Int_set& s);

  // Returns the first valid iterator.
  Iterator beg() const;

  // Returns the iterator next to the last valid iterator.
  Iterator end() const;

  // Returns the element pointed by i.
  // Aborts if i is not a valid iterator.
  int value(Iterator i) const;


  ////////////////////////
  //// Class Iterator ////
  ////////////////////////

  // Class for iterating over the elements of sets.

  class Iterator {

  public:

    explicit Iterator(int i);
    Iterator(const Iterator& i);
    void operator=(const Iterator& i);

    void next(const Int_set& s);

    bool operator==(Iterator i) const;
    bool operator!=(Iterator i) const;

  private:

    int iter;
    friend class Int_set;

  }; // End of class Iterator.

private:

  Vec<int> support; 

  // Pointer (possibly invalid) to corresponding entry in support. 
  Vec<int> pointer; 

  friend class Iterator;

}; // End of class Int_set.

ostream& operator<<(ostream& out, const Int_set& s);

} // namespace FF

#endif // FF_INT_SET_DEFS_HPP

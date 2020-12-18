/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file Sort.hpp
 *
 * @since 06/05/2002
 * @since 16/07/2003 flight Moscow-London, changed from a
 *   previous single-type version.
 */


#ifndef __Sort__
#  define __Sort__

#include "Debug/Assertion.hpp"
#include "Debug/Tracer.hpp"

#include "Allocator.hpp"
#include "DArray.hpp"

namespace Lib {

struct DefaultComparator
{
  template<typename T>
  static Comparison compare(T a, T b)
  {
    CALL("DefaultComparator::compare");

    if(a==b) {
      return EQUAL;
    }
    else if(a<b) {
      return LESS;
    }
    else {
      ASS(a>b);
      return GREATER;
    }
  }
};

template <class Comparator, typename C>
void sort(C* first, C* afterLast)
{
  CALL("sort");
  //modified sorting code, that was originally in Resolution::Tautology::sort

  C* arr=first;
  size_t size=afterLast-first;
  if(size<=1) {
    //nothing to sort
    return;
  }

  // array behaves as a stack of calls to quicksort
  static DArray<size_t> ft(32);

  size_t from = 0;
  size_t to=size-1;
  ft.ensure(to);

  size_t p = 0; // pointer to the next element in ft
  for (;;) {
    ASS(from<size && to<size); //checking for underflows
    // invariant: from < to
    size_t m = from + Random::getInteger(to-from+1);
    C mid = arr[m];
    size_t l = from;
    size_t r = to;
    while (l < m) {
      switch (Comparator::compare(arr[l],mid))
	{
	case EQUAL:
	case LESS:
	  l++;
	  break;
	case GREATER:
	  if (m == r) {
	    arr[m] = arr[l];
	    arr[l] = arr[m-1];
	    arr[m-1] = mid;
	    m--;
	    r--;
	  }
	  else {
	    ASS(m < r);
	    C aux = arr[l];
	    arr[l] = arr[r];
	    arr[r] = aux;
	    r--;
	  }
	  break;
	}
    }
    // l == m
    // now literals in lits[from ... m-1] are smaller than lits[m]
    // and literals in lits[r+1 ... to] are greater than lits[m]
    while (m < r) {
      switch (Comparator::compare(mid,arr[m+1]))
	{
	case LESS:
	  {
	    C aux = arr[r];
	    arr[r] = arr[m+1];
	    arr[m+1] = aux;
	    r--;
	  }
	  break;
	case EQUAL:
	case GREATER:
	  arr[m] = arr[m+1];
	  arr[m+1] = mid;
	  m++;
	}
    }
    // now literals in lits[from ... m-1] are smaller than lits[m]
    // and all literals in lits[m+1 ... to] are greater than lits[m]
    if (m+1 < to) {
      ft[p++] = m+1;
      ft[p++] = to;
    }

    to = m-1;
    if (m!=0 && from < to) {
      continue;
    }
    if (p != 0) {
      p -= 2;
      ASS(p >= 0);
      from = ft[p];
      to = ft[p+1];
      continue;
    }
    return;
  }
}

/**
 * A template class to sort data. The type ToCompare is the
 * type of elements to sort. The type Comparator is the class that
 * contains a function bool lessThan(ToCompare, ToCompare).
 * A typical work with this class is as follows:
 *
 * <ol>
 *  <li>a comparator c and an element s of the class Sort are created;</li>
 *  <li>elements of the class ToCompare are added one by one;</li>
 *  <li>s.sort() is called</li>
 *  <li>the resulting sorted collection is read.</li>
 * </ol>
 * @since 16/07/2003 flight Moscow-London, changed from a
 * previous one-type version.
 * @since 03/04/2004 Torrevieja, changed to use a comparator instead of
 *  a static function
 */
template <typename ToCompare, class Comparator>
class Sort
{
 public:
  /**
   * Initialize the sort element.
   *
   * @param length the number of elements to sort
   * @param comparator object used for comparison
   */
  Sort (int length,Comparator& comparator)
    :
    _size(length),
    _length(0),
    _comparator(comparator)
    {
      CALL("Sort::Sort");

      void* mem = ALLOC_KNOWN(length*sizeof(ToCompare),"Sort<>");
      _elems = array_new<ToCompare>(mem, length);
    }

  inline ~Sort ()
  {
    CALL("Sort::~Sort");

    array_delete(_elems,_size);
    DEALLOC_KNOWN(_elems,_size*sizeof(ToCompare),"Sort<>");
  }

  /**
   * Return the length (the number of elements to sort)
   */
  inline int length () const { return _length; }

  /**
   * Return the nth element, used to retrieve sorted elements
   */
  inline ToCompare operator [] (int n) const
    {
      ASS(n < _length);
      return _elems[n];
    } // Sort::operator []

  /**
   * Add an element to sort.
   *
   * @param elem the element.
   */
  inline void add (ToCompare elem)
    {
      ASS(_length < _size);

      _elems[_length++] = elem;
    } // Sort::add

  /**
   * Sort elements.
   */
  inline void sort ()
  {
    CALL("Sort::sort/0");
    sort (0,_length-1);
  }

  /**
   * Check membership in the sorted list. Membership is checked using
   * == for equality.
   *
   * @return true if elem is the member of Sort
   * @since 17/07/2003 Manchester, changed to the new two-argument Sort class
   */
   inline bool member (const ToCompare elem) const {
     return member (elem,0,_length-1);
   }

 protected:  // structure
  /** array of elements */
  ToCompare* _elems;
  /** capacity */
  int _size;
  /** the number of elements */
  int _length;
  /** object used to compare elements */
  Comparator& _comparator;

  /**
   * Quicksort elements between, and including indexes p and r, was taken
   * from the Rivest et al. book - never use this book for practical
   * algorithms :)
   * @since 16/04/2006 Bellevue, improved: the algorithm sometimes
   * compared elements with themselves
   * @since 27/06/2008 Manchester, replaced since the old one was showing
   *   quadratic behaviour
   */
  void sort(int p,int r)
  {
    CALL("Sort::sort/2");
    ASS(r < _length);

    if (p >= r) {
      return;
    }
    int m = (p+r)/2;
    int i = p;
    int j = r;
    ToCompare a = _elems[m];
    while (i < m) {
      ToCompare b = _elems[i];
      if (! _comparator.lessThan(a,b)) { // a[i] <= a[m]
	i++;
	continue;
      }
      if (m < j) {
	_elems[i] = _elems[j];
	_elems[j] = b;
	j--;
	continue;
      }
      _elems[m] = b;
      _elems[i] = _elems[m-1];
      m--;
      j--;
    }
    while (m < j) {
      ToCompare b = _elems[j];
      if (! _comparator.lessThan(b,a)) { // a[m] <= a[j]
	j--;
	continue;
      }
      _elems[m] = b;
      _elems[j] = _elems[m+1];
      m++;
    }
    _elems[m] = a;
    sort(p,m-1);
    sort(m+1,r);
  } // sort

  /**
   * Check membership in the sorted list between the indexes fst
   * and snd. Membership is checked using == for equality. The function
   * works correctly only if lessThan is a total order.
   *
   * @return true if elem is the member of Sort[fst] ... Sort[snd]
   * @since 17/07/2003 Manchester, changed to the new two-argument Sort class
   */
  bool member (const ToCompare elem, int fst, int lst) const
  {
    CALL("Sort::member");

    for (;;) {
      if (fst > lst) {
	return false;
      }

      int mid = (fst + lst) / 2;

      if (_elems[mid] == elem) {
	return true;
      }

      if (_comparator.lessThan(_elems[mid],elem)) {
	lst = mid-1;
      }
      else { // _elems[mid] > c
	fst = mid+1;
      }
    }
  } // Sort::member
};  // class Sort

} // namespace Lib

#endif



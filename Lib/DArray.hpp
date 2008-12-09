/**
 * @file DArray.hpp
 * Defines a class of self-deallocating arrays. They should be used instead
 * of Array when the size is known in advance
 *
 * @since 30/12/2007 Manchester
 */

#ifndef __DArray__
#define __DArray__

#include "../Debug/Assertion.hpp"

#include "Allocator.hpp"
#include "Comparison.hpp"
#include "Random.hpp"

namespace Lib {

/**
 * Class of fixed-size self-deallocating generic arrays.
 * @param C the type of content
 * @since 30/12/2007 Manchester
 */
template<typename C>
class DArray
{
private:
  //private and undefined operator= and copy constructor to avoid implicitly generated ones
  DArray(const DArray&);
  DArray& operator=(const DArray&);
public:
  /**
   * Create an array having the given @b size
   * @since 30/12/2007 Manchester
   */
  inline
  DArray (size_t size)
    : _size(size)
  {
    ASS(size > 0);
    void* mem = ALLOC_KNOWN(sizeof(C)*size,"DArray<>");
    _array = new(mem) C[size];
  }

  /** Delete array */
  inline ~DArray()
  {
    DEALLOC_KNOWN(_array,sizeof(C)*_size,"DArray<>");
  }

  /** Return a reference to the n-th element of the array */
  inline C& operator[] (size_t n)
  {
    ASS(n < _size);
    return _array[n];
  } // operator[]

  /** Return a reference to the n-th element of the array */
  inline const C& operator[](size_t n) const
  {
    ASS(n < _size);
    return _array[n];
  }

  /** return the standard array represented by this DArray */
  inline C* array () { return _array; }

  /**
   * Ensure that the array's size is at least @b s. If the size
   * is smaller the array will expand.
   * @warning upon extension no copying of elements will be done
   *   so the operation is safe only before processing the array.
   * @since 02/01/2008 Manchester
   */
  inline void ensure(size_t s)
  {
    if (_size >= s) {
      return;
    }

    DEALLOC_KNOWN(_array,sizeof(C)*_size,"DArray<>");
    _size = s;
    void* mem = ALLOC_KNOWN(sizeof(C)*s,"DArray<>");
    _array = new(mem) C[s];
  } // ensure

  /** Return the size (the capacity) of the array */
  size_t size() const { return _size; }

  /** Ensure that the array's size is at least @b count and
   * initialize first @b count elements of the array to @b value. */
  void init(size_t count, const C& value) {
    CALL("DArray::init");

    ensure(count);
    C* ptr=_array+count;
    while(ptr!=_array) {
      *(--ptr)=value;
    }
  }

  /**
   * Ensure that the array's size is at least @b count and
   * initialize first @b count elements with halues from @b src.
   *
   * @b src has to support C operator[](size_t).
   */
  /**  */
  template<typename Arr>
  void initFromArray(size_t count, Arr& src) {
    CALL("DArray::initFromArray");

    ensure(count);
    C* ptr=_array+count;
    while(count) {
      *(--ptr)=src[--count];
    }
  }

  /**
   * Sort first @b count items using @b Comparator::compare
   * as comparator.
   */
  template<typename Comparator>
  void sort(size_t count)
  {
    //modified sorting code, that was originally in Resolution::Tautology::sort

    // array behaves as a stack of calls to quicksort
    static DArray<size_t> ft(32);

    size_t from = 0;
    size_t to=count-1;
    ft.ensure(to);

    size_t p = 0; // pointer to the next element in ft
    for (;;) {
      ASS(from<count && to<count); //checking for underflows
      // invariant: from < to
      size_t m = from + Random::getInteger(to-from+1);
      C mid = (*this)[m];
      size_t l = from;
      size_t r = to;
      while (l < m) {
        switch (Comparator::compare((*this)[l],mid))
  	{
  	case EQUAL:
  	case LESS:
  	  l++;
  	  break;
  	case GREATER:
  	  if (m == r) {
  	    (*this)[m] = (*this)[l];
  	    (*this)[l] = (*this)[m-1];
  	    (*this)[m-1] = mid;
  	    m--;
  	    r--;
  	  }
  	  else {
  	    ASS(m < r);
  	    C aux = (*this)[l];
  	    (*this)[l] = (*this)[r];
  	    (*this)[r] = aux;
  	    r--;
  	  }
  	  break;
  	}
      }
      // l == m
      // now literals in lits[from ... m-1] are smaller than lits[m]
      // and literals in lits[r+1 ... to] are greater than lits[m]
      while (m < r) {
        switch (Comparator::compare(mid,(*this)[m+1]))
  	{
  	case LESS:
  	  {
  	    C aux = (*this)[r];
  	    (*this)[r] = (*this)[m+1];
  	    (*this)[m+1] = aux;
  	    r--;
  	  }
  	  break;
  	case EQUAL:
  	case GREATER:
  	  (*this)[m] = (*this)[m+1];
  	  (*this)[m+1] = mid;
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

protected:
  /** current array's size */
  size_t _size;
  /** array's content */
  C* _array;
}; // class DArray

} // namespace Lib

#endif

/**
 * @file DArray.hpp
 * Defines a class of self-deallocating arrays. They should be used instead
 * of Array when the size is known in advance
 *
 * @since 30/12/2007 Manchester
 */

#ifndef __DArray__
#define __DArray__

#include "../Forwards.hpp"
#include "../Debug/Assertion.hpp"

#include "Allocator.hpp"
#include "Comparison.hpp"
#include "Random.hpp"
#include "Reflection.hpp"
#include "VirtualIterator.hpp"

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
  class Iterator;

  DECL_ELEMENT_TYPE(C);
  DECL_ITERATOR_TYPE(Iterator);
  /**
   * Create an array having the given @b size
   * @since 30/12/2007 Manchester
   */
  inline
  DArray (size_t size)
    : _size(size), _capacity(size)
  {
    ASS(size > 0);
    void* mem = ALLOC_KNOWN(sizeof(C)*_capacity,"DArray<>");
    _array = new(mem) C[_capacity];
  }

  /** Delete array */
  inline ~DArray()
  {
    C* p=_array+_capacity;
    while(p!=_array) {
      (--p)->~C();
    }
    DEALLOC_KNOWN(_array,sizeof(C)*_capacity,"DArray<>");
  }

  /** Return a reference to the n-th element of the array */
  inline C& operator[] (size_t n)
  {
    ASS_L(n,_size);
    return _array[n];
  } // operator[]

  /** Return a reference to the n-th element of the array */
  inline const C& operator[](size_t n) const
  {
    ASS_L(n,_size);
    return _array[n];
  }

  /** return the standard array represented by this DArray */
  inline C* array () { return _array; }

  inline C* begin() { return _array; }
  inline C* end() { return _array+_size; }



  /**
   * Set array's size to @b s and that its capacity is at least @b s.
   * Return true iff array was not extended.
   * If the capacity is smaller, the array will be extended.
   *
   * @warning upon extension no copying of elements will be done
   *   so the operation is safe only before processing the array.
   * @since 02/01/2008 Manchester
   */
  inline bool ensure(size_t s)
  {
    _size = s;
    if (_capacity >= _size) {
      return true;
    }

    C* p=_array+_capacity;
    while(p!=_array) {
      (--p)->~C();
    }
    DEALLOC_KNOWN(_array,sizeof(C)*_capacity,"DArray<>");
    _capacity = _size;
    void* mem = ALLOC_KNOWN(sizeof(C)*_capacity,"DArray<>");
    _array = new(mem) C[_capacity];
    return false;
  } // ensure

  /**
   * Set array's size to @b s and that its capacity is at least @b s.
   * If the capacity is smaller, the array will expand, and all old
   * elements will be copied to the new array.
   *
   */
  void expand(size_t s)
  {
    if (_capacity >= s) {
      _size = s;
      return;
    }

    size_t oldCapacity=_capacity;
    C* oldArr = _array;

    _capacity = max(s, _capacity*2);
    void* mem = ALLOC_KNOWN(sizeof(C)*_capacity,"DArray<>");
    _array = static_cast<C*>(mem);

    C* optr=oldArr;
    C* nptr=_array;
    C* firstEmpty=_array+_size;
    C* afterLast=_array+_capacity;
    while(nptr!=firstEmpty) {
      new(nptr++) C( *optr );
      (optr++)->~C();
    }
    while(nptr!=afterLast) {
      new(nptr++) C();
    }
    _size = s;

    DEALLOC_KNOWN(oldArr,sizeof(C)*oldCapacity,"DArray<>");
  } // ensure

  /** Return the ensured size of the array */
  inline size_t size() const { return _size; }

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
   * Initialize array by elements of the iterator. Size of the array
   * will be equal to number of elements of the iterator.
   */
  template<class It>
  void initFromIterator(It it, size_t count=0) {
    CALL("DArray::initFromIterator");

    if(count) {
      ensure(count);
      C* ptr=_array;
      while(it.hasNext()) {
	*(ptr++)=it.next();
      }
    } else {
      ensure(0);
      count=0;
      while(it.hasNext()) {
	expand(++count);
	(*this)[count-1]=it.next();
      }
    }
  }


  /**
   * Sort first @b count items using @b Comparator::compare
   * as comparator.
   */
  template<typename Comparator>
  inline void sort(Comparator comp)
  {
    sortGen<false>(comp);
  }

  template<typename Comparator>
  inline void sortInversed(Comparator comp)
  {
    sortGen<true>(comp);
  }

  template<bool Inversed, typename Comparator>
  void sortGen(Comparator comp)
  {
    //modified sorting code, that was originally in Resolution::Tautology::sort

    // array behaves as a stack of calls to quicksort
    static DArray<size_t> ft(32);

    size_t from = 0;
    size_t to=size()-1;
    ft.ensure(to);

    size_t p = 0; // pointer to the next element in ft
    for (;;) {
      ASS(from<size() && to<size()); //checking for underflows
      // invariant: from < to
      size_t m = from + Random::getInteger(to-from+1);
      C mid = (*this)[m];
      size_t l = from;
      size_t r = to;
      while (l < m) {
        switch ((Inversed?-1:1)*comp.compare((*this)[l],mid))
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
        switch ((Inversed?-1:1)*comp.compare(mid,(*this)[m+1]))
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
  /** capacity of currently allocated piece of memory */
  size_t _capacity;
  /** array's content */
  C* _array;

public:
  class Iterator
  {
  public:
    DECL_ELEMENT_TYPE(C);
    inline Iterator() : _next(0), _afterLast(0) {}
    inline Iterator(DArray& arr) : _next(arr._array),
    _afterLast(arr._array+arr._size) {}
    inline bool hasNext() { return _next!=_afterLast; }
    inline C next() { return *(_next++); }
  private:
    C* _next;
    C* _afterLast;
  };
  class ReversedIterator
  {
  public:
    DECL_ELEMENT_TYPE(C);
    inline ReversedIterator(DArray& arr) : _curr(arr._array+arr._size),
    _first(arr._array) {}
    inline bool hasNext() { return _curr!=_first; }
    inline C next() { return *(--_curr); }
  private:
    C* _curr;
    C* _first;
  };
}; // class DArray

template<typename T>
VirtualIterator<T> getContentIterator(DArray<T>& arr)
{
  return pvi( typename DArray<T>::Iterator(arr) );
}

} // namespace Lib

#endif

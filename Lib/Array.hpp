/**
 * @file Array.hpp
 * Defines a class of flexible-sized arrays
 *
 * @since 04/06/2005 Manchester
 */

#ifndef __Array__
#define __Array__

#include "../Debug/Assertion.hpp"

#include "../Lib/Allocator.hpp"

namespace Lib {

class EmptyInitializer;

/**
 * Class of flexible-size generic arrays.
 * @since 11/03/2006 Bellevue
 * @since 26/12/2007 Manchester, reimplemented using a virtual function for
 *    filling new elements
 *
 * Initializer is a class with a static method
 *
 * static void fillInterval (Array* arr, size_t start, size_t end)
 *
 * that initializes elements arr[start],...,arr[end-1].
 *
 */
template<typename C, class Initializer=EmptyInitializer>
class Array
{
public:
  /**
   * Create an array having initialCapacity.
   */
  inline
  Array (size_t initialCapacity)
    : _capacity(initialCapacity)
  {
    if(initialCapacity) {
      void* mem = ALLOC_KNOWN(initialCapacity*sizeof(C),"Array<>");
      _array = new(mem) C[initialCapacity];
      Initializer::fillInterval(this, 0, _capacity);
    } else {
      _array=0;
    }
  }

  /**
   * Create an array having the initial capacity 31
   * @since 04/01/2008 flight Manchester-Murcia
   */
  inline Array ()
    : _capacity(31)
  {
    void* mem = ALLOC_KNOWN(sizeof(C)*31,"Array<>");
    _array = new(mem) C[31];
    Initializer::fillInterval(this, 0, _capacity);
  }


  /**
   * Delete array.
   * @since 02/01/2007 Manchester, fixing a long-standing memory leak
   */
  virtual ~Array()
  {
    if(_array) {
      DEALLOC_KNOWN(_array,_capacity*sizeof(C),"Array<>");
    }
  }

  /** Return a reference to the n-th element of the array,
   *  expand the array if necessary. If it is guaranteed that @b n is a valid index
   *  then set() can be used instead.
   */
  inline
  C& operator[] (size_t n)
  {
    if (n >= _capacity) {
      expandToFit(n);
    }
    return _array[n];
  } // operator[]

  /** Return a reference to the n-th element of the array. @b n must be a valid
   *  index in the array. If the index may be invalid, use get() instead
   */
  inline const C& operator[](size_t n) const
  {
    ASS(n < _capacity);

    return _array[n];
  }

  /**
   * Return the n-th element of the array. Expand if necessary.
   * @since 23/03/2007 Manchester
   */
  inline C get(size_t n)
  {
    if (n >= _capacity) {
      expandToFit(n);
    }

    return _array[n];
  }

  /**
   * Set the @b n-th element to @b value. No check is made whether @b n exceeds the
   * array bound.
   * @since 23/03/2007 Manchester
   */
  inline void set (size_t n,C value)
  {
    ASS(n < _capacity);

    _array[n] = value;
  } // set

  /** A pointer to the content (the real array), extremely unsafe! */
  inline const C* content() { return _array; }

  /** Return the size (the capacity) of the array */
  size_t size() const { return _capacity; }

  inline C* begin() { return _array; }

  inline C* end() { return _array+_capacity; }


protected:
  /** current array's capacity */
  size_t _capacity;
  /** array's content */
  C* _array;

  /**
   * Expand the array to fit n-th element.
   * @since 11/03/2006 Redmond
   */
  void expandToFit (size_t n)
  {
    ASS(n >= _capacity);

    // determine new capacity (at least double the old one)
    size_t newCapacity = 2 * _capacity;
    if (newCapacity <= n) {
      newCapacity = n+1;
    }

    // allocate new array and copy old array's content to the new place
    void* mem = ALLOC_KNOWN(sizeof(C)*newCapacity,"Array<>");
    C* newArray = new(mem) C[newCapacity];
    if(_capacity) {
      for (int i = _capacity-1;i >= 0;i--) {
	newArray[i] = _array[i];
      }
    }
    // deallocate the old array
    DEALLOC_KNOWN(_array,_capacity*sizeof(C),"Array<>");
    _array = newArray;
    size_t oldCapacity=_capacity;
    _capacity = newCapacity;
    Initializer::fillInterval(this, oldCapacity, _capacity);
  } // Array::expandToFit
};


struct EmptyInitializer
{
  template<typename C>
  static void fillInterval (Array<C,EmptyInitializer>* arr, size_t start,size_t end)
  {
  }
};

struct ZeroInitializer
{
  template<typename C>
  static void fillInterval (Array<C,ZeroInitializer>* arr, size_t start,size_t end)
  {
    for(size_t i=start; i<end; i++) {
      (*arr)[i]=0;
    }
  }
};


} // namespace Lib

#endif

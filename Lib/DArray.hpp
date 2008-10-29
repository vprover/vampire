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

namespace Lib {

/**
 * Class of fixed-size self-deallocating generic arrays.
 * @param C the type of content
 * @since 30/12/2007 Manchester
 */
template<typename C>
class DArray
{
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

protected:
  /** current array's size */
  size_t _size;
  /** array's content */
  C* _array;
}; // class DArray

} // namespace Lib

#endif

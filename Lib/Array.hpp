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
 * @file Array.hpp
 * Defines a class of flexible-sized arrays
 *
 * @since 04/06/2005 Manchester
 */

#ifndef __Array__
#define __Array__

#include "Debug/Assertion.hpp"

#include "Lib/Allocator.hpp"
#include <initializer_list>
#include <utility>
#include <iostream>

namespace Lib {

/**
 * Class of flexible-size generic arrays.
 * @since 11/03/2006 Bellevue
 * @since 26/12/2007 Manchester, reimplemented using a virtual function for
 *    filling new elements
 */
template<typename C>
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
      _array = array_new<C>(mem, initialCapacity);
    } else {
      _array=0;
    }
  }

  inline
  Array (std::initializer_list<C> contents)
    : Array(contents.size()) 
  {
    auto iter = contents.begin();
    unsigned i = 0;
    while(iter != contents.end()) {
      ASS(i < _capacity)
      _array[i] = std::move(*iter);
      iter++;
      i++;
    }
  }

  /**
   * Copy-construct array, by copying the content.
   */
  Array (const Array &o) : _capacity(o._capacity) {
    if (o._array) {
      void* mem = ALLOC_KNOWN(_capacity*sizeof(C),"Array<>");
      _array = static_cast<C*>(mem);
      for(size_t i=0; i<_capacity; i++) {
        new(&_array[i]) C(o._array[i]);
      }
    } else {
      _array = 0;
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
    _array = array_new<C>(mem, 31);
  }

  /**
   * Fill the array by initial values at positions between start and end-1
   * @since 26/12/2007 Manchester
   */
  virtual void fillInterval (size_t start,size_t end)
  {
  } // fillInterval

  /**
   * Delete array.
   * @since 02/01/2007 Manchester, fixing a long-standing memory leak
   */
  virtual ~Array()
  {
    CALL("Array::~Array()");

    if(_array) {
      array_delete(_array, _capacity);
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
  inline C& get(size_t n)
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

  inline C const* begin() const { return _array; }
  inline C const* end()   const { return _array+_capacity; }


  friend std::ostream& operator<<(std::ostream& out, Array const& self) 
  {
    auto iter = self.begin();
    out << "[ ";
    if (iter != self.end()) {
      out << *iter++;
      while (iter != self.end()) {
        out << ", ";
        out << *iter++;
      }
    }
    out << " ]";
    return out;
  }

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
    CALL("Array::expandToFit");
    ASS(n >= _capacity);

    // determine new capacity (at least double the old one)
    size_t newCapacity = 2 * _capacity;
    if (newCapacity <= n) {
      newCapacity = n+1;
    }

    // allocate new array and copy old array's content to the new place
    void* mem = ALLOC_KNOWN(sizeof(C)*newCapacity,"Array<>");
    C* newArray = array_new<C>(mem, newCapacity);
    if(_capacity) {
      for (int i = _capacity-1;i >= 0;i--) {
	newArray[i] = _array[i];
      }
    }

    if(_array) {
      // deallocate the old array
      array_delete(_array,_capacity);
      DEALLOC_KNOWN(_array,_capacity*sizeof(C),"Array<>");
    }

    _array = newArray;
    fillInterval(_capacity,newCapacity);
    _capacity = newCapacity;
  } // Array::expandToFit
};

/**
 * Class of flexible-size generic arrays whose elements
 * are being initialized to zero. (Zero-Initialized Array)
 */
template <typename T>
class ZIArray
: public Array<T>
{
public:
  inline
  ZIArray(size_t initialCapacity) : Array<T>(initialCapacity)
  {
    fillInterval(0, Array<T>::_capacity);
  }
  inline
  ZIArray()
  {
    fillInterval(0, Array<T>::_capacity);
  }


  void fillInterval(size_t start,size_t end)
  {
    for(size_t i=start; i<end; i++) {
      Array<T>::_array[i]=static_cast<T>(0);
    }
  }

};

} // namespace Lib

#endif

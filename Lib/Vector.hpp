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
 * @file Vector.hpp
 * Defines a class of constant-size generic vectors. The size is given as an
 * argument when we allocate the vector.
 *
 * @since 01/02/2008 Manchester
 */

#ifndef __Vector__
#define __Vector__

#include "Forwards.hpp"

#include "Debug/Assertion.hpp"
#include "Allocator.hpp"
#include "VString.hpp"

namespace Lib {

using namespace std;

/**
 * Class of constant size generic vectors. The size of a vector is fixed when it
 * is allocated and cannot change, unlike that of arrays. Vectors of size 0 are
 * not allowed.
 * @since 01/02/2008 Manchester
 */
template<typename C>
class Vector
{
public:
  /** Return a reference to the n-th element of the vector */
  inline C& operator[] (size_t n)
  {
    ASS(n < _length);
    return _array[n];
  } // operator[]

  /** Return a reference to the n-th element of the array */
  inline const C& operator[](size_t n) const
  {
    ASS(n < _length);
    return _array[n];
  }

  /** Return the length (the capacity) of the array */
  size_t length() const { return _length; }

  /** allocate a vector of the size @b length */
  static Vector* allocate(size_t length)
  {
    CALL("Vector::allocate");
    ASS_G(length,0);

    size_t sz=sizeof(Vector) + (length-1)*sizeof(C);
    Vector* v = reinterpret_cast<Vector*>(ALLOC_KNOWN(sz,"Vector"));
    v->_length = length;
    C* arr = v->_array;
    // in the case C is a class with an initialiser, apply the constructor of it
    // to every element of the allocated array
    array_new<C>(arr,length);
    return v;
  } // allocate

  /** deallocate the vector */
  void deallocate()
  {
    CALL("Vector::deallocate");

    // in the case C is a class with an initialiser, apply the destructor of it
    // to every element of the allocated array
    array_delete(_array, _length);
    size_t sz=sizeof(Vector) + (_length-1)*sizeof(C);
    DEALLOC_KNOWN(this,sz,"Vector");
  } // deallocate

  bool operator==(const Vector& v) const
  {
    CALL("Vector::operator==");

    if(length()!=v.length()) {
      return false;
    }
    size_t sz = length();
    for(size_t i=0; i!=sz; ++i) {
      if((*this)[i]!=v[i]) {
        return false;
      }
    }
    return true;
  }

  bool operator!=(const Vector& o) const
  { return !((*this)==o); }

  /**
   * Convert the vector to its string representation. To use this function,
   * elements must have a toString() function too.
   */
  vstring toString()
  {
    vstring res;
    for(size_t i=0;i<_length;i++) {
      if (i>0) {
	res+=",";
      }
      res+=(*this)[i].toString();
    }
    return res;
  } // toString

  friend class Indexing::CodeTree;
  friend class Indexing::ClauseCodeTree;

  /**
   * Iterator that deallocates the vector when it yields the last value.
   */
  class DestructiveIterator
  {
  public:
    DECL_ELEMENT_TYPE(C);

    DestructiveIterator(Vector& v)
    : cur(v._array), afterLast(v._array+v.length()), vec(&v)
    {
      if (cur==afterLast) {
	vec->deallocate();
      }
    }

    bool hasNext()
    {
      return cur!=afterLast;
    }

    C next()
    {
      CALL("Vector::DestructiveIterator::next");
      ASS(hasNext());

      C res=*cur;
      cur++;
      if (cur==afterLast) {
	vec->deallocate();
      }
      return res;
    }
  private:
    C* cur;
    C* afterLast;
    Vector* vec;
  }; // Vector::DestructiveIterator
protected:
  /** array's length */
  size_t _length;
  /** array's content */
  C _array[1];
private:
  /** declared but not defined to prevent its use */
  void* operator new(size_t,size_t length);
  /** not used, will cause an assertion violation */
  void operator delete(void*)
  {
    ASSERTION_VIOLATION
  }
  /** declared but not defined to prevent its use */
  Vector();
}; // class Vector

} // namespace Lib

#endif

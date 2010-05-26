/**
 * @file Vector.hpp
 * Defines a class of variable-size generic vectors
 *
 * @since 01/02/2008 Manchester
 */

#ifndef __Vector__
#define __Vector__

#include <string>

#include "Forwards.hpp"

#include "Debug/Assertion.hpp"
#include "Allocator.hpp"

namespace Lib {

using namespace std;

/**
 * Class of variable-size generic vectors
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

    //We have to get sizeof(Vector) + (_length-1)*sizeof(C)
    //this way, because _length-1 wouldn't behave well for
    //_length==0 on x64 platform.
    size_t sz=sizeof(Vector) + length*sizeof(C);
    sz-=sizeof(C);

    Vector* v = reinterpret_cast<Vector*>(ALLOC_KNOWN(sz, "Vector"));
    v->_length = length;
    C* arr = v->_array;
    array_new<C>(arr, length);
    return v;
  } // allocate

  /** deallocate the vector */
  void deallocate()
  {
    CALL("Vector::deallocate");

    array_delete(_array, _length);

    //We have to get sizeof(Vector) + (_length-1)*sizeof(C)
    //this way, because _length-1 wouldn't behave well for
    //_length==0 on x64 platform.
    size_t sz=sizeof(Vector) + _length*sizeof(C);
    sz-=sizeof(C);

    DEALLOC_KNOWN(this,sz,"Vector");
  } // deallocate


  string toString()
  {
    string res;
    for(size_t i=0;i<_length;i++) {
      if(i>0) {
	res+=",";
      }
      res+=(*this)[i].toString();
    }
    return res;
  }

  friend class Indexing::CodeTree;
  friend class Indexing::ClauseCodeTree;

  /**
   * Iterator that deallocates the vector when it yields the last value.
   *
   * @warning if the Vector is of length zero, it is deallocated in the
   *   	      constructor of the iterator.
   */
  class DestructiveIterator
  {
  public:
    DECL_ELEMENT_TYPE(C);

    DestructiveIterator(Vector& v)
    : cur(v._array), afterLast(v._array+v.length()), vec(&v)
    {
      if(cur==afterLast) {
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
      if(cur==afterLast) {
	vec->deallocate();
      }
      return res;
    }
  private:
    C* cur;
    C* afterLast;
    Vector* vec;
  };
protected:
  /** array's length */
  size_t _length;
  /** array's content */
  C _array[1];
private:
  void* operator new(size_t,size_t length);
  void operator delete(void*)
  {
    ASSERTION_VIOLATION
  }
  Vector();
}; // class Vector

} // namespace Lib

#endif

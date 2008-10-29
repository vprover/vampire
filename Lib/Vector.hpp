/**
 * @file Vector.hpp
 * Defines a class of variable-size generic vectors
 *
 * @since 01/02/2008 Manchester
 */

#ifndef __Vector__
#define __Vector__

#include "../Debug/Assertion.hpp"
#include "Allocator.hpp"

namespace Lib {

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

    Vector* v = reinterpret_cast<Vector*>(ALLOC_KNOWN(sizeof(Vector) + 
						      (length-1)*sizeof(C),
						      "Vector"));
    v->_length = length;
    C* arr = v->_array;
    new(arr) C[length];
    return v;
  } // allocate

  /** deallocate the vector */
  void deallocate()
  {
    CALL("Vector::deallocate");

    for (int i = _length-1;i >= 0;i--) {
      _array[i].~C();
    }
    DEALLOC_KNOWN(this,(sizeof(Vector) + (_length-1)*sizeof(C)),"Vector");
  } // deallocate

  void* operator new(size_t,size_t length);
  void operator delete(void*)
  {
    ASS(false);
  }
  Vector();

protected:
  /** array's length */
  size_t _length;
  /** array's content */
  C _array[1];
}; // class Vector

} // namespace Lib

#endif

/**
 * @file TriangularArray.hpp
 * Defines class TriangularArray.
 */


#ifndef __TriangularArray__
#define __TriangularArray__

#include "Allocator.hpp"

namespace Lib {

template<typename T>
class TriangularArray
{
private:
  //private and undefined operator= and copy constructor to avoid implicitly generated ones
  TriangularArray(const TriangularArray&);
  TriangularArray& operator=(const TriangularArray&);
public:
  TriangularArray(size_t side)
  : _2sideMinus1(2*side-1)
  {
    _data=static_cast<T*>(ALLOC_KNOWN(dataSize()*sizeof(void*), "Lib::TriangularArray"));
  }
  ~TriangularArray()
  {
    DEALLOC_KNOWN(_data,dataSize()*sizeof(void*), "Lib::TriangularArray");
  }

  inline
  size_t dataSize() const
  {
    return ((_2sideMinus1+1)*(_2sideMinus1+3)) / 8;
  }

  T& get(size_t x, size_t y)
  {
    ASS_GE(x,y);
    ASS_L(x,(_2sideMinus1+1)/2);
    return _data[x + (y*(_2sideMinus1-y))/2];
  }

  void set(size_t x, size_t y, T val)
  {
    ASS_GE(x,y);
    ASS_L(x,(_2sideMinus1+1)/2);
    _data[x + (y*(_2sideMinus1-y))/2]=val;
  }



private:
  /**
   * It's more convenient to have the side times two minus 1,
   * than simply side, as we save two operations in the
   * access operation.
   */
  size_t _2sideMinus1;
  T* _data;
};

};

#endif /* __TriangularArray__ */

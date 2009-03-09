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
  : _2sidePlus1(2*side+1)
  {
    _data=ALLOC_KNOWN(dataSize(), "Lib::TriangularArray");
  }
  ~TriangularArray()
  {
    DEALLOC_KNOWN(_data,dataSize(), "Lib::TriangularArray");
  }

  inline
  size_t dataSize() const
  {
    return ((_2sidePlus1-1)*(_2sidePlus1+1)) / 8;
  }

  T& operator[] (size_t x, size_t y)
  {
    return _data[x + (y*(_2sidePlus1-y))/2];
  }


private:
  /**
   * It's more convenient to have the side times two,
   * than simply side, as we save one operation in the
   * access operation.
   */
  size_t _2sidePlus1;
  T* _data;
};

};

#endif /* __TriangularArray__ */

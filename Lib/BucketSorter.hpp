/**
 * @file BucketSorter.hpp
 * Defines class BucketSorter.
 */


#ifndef __BucketSorter__
#define __BucketSorter__

#include "Stack.hpp"

namespace Lib {

template<typename T, class Evaluator>
class BucketSorter
{
public:
  BucketSorter(size_t bucketCnt)
  : _bucketCnt(bucketCnt), _size(0), _minOccupied(bucketCnt)
  {
    _buckets=static_cast<Stack<T>*>(ALLOC_KNOWN(_bucketCnt*sizeof(Stack<T>), "BucketSorter"));
    for(unsigned i=0;i<_bucketCnt;i++) {
      new (&_buckets[i]) Stack<T>(8);
    }
  }
  ~BucketSorter()
  {
    for(unsigned i=0;i<_bucketCnt;i++) {
      _buckets[i].~Stack<T>();
    }
    DEALLOC_KNOWN(_buckets, _bucketCnt*sizeof(Stack<T>), "BucketSorter");
  }

  inline bool isEmpty() { return _size==0; }

  void insert(T obj)
  {
    _size++;
    size_t i=Evaluator::eval(obj);
    _buckets[i].push(obj);
    if(i<_minOccupied) {
      _minOccupied=i;
    }
  }
  T pop()
  {
    ASS_G(_size,0);
    _size--;
    T res=_buckets[_minOccupied].pop();
    if(_buckets[_minOccupied].isEmpty()) {
      if(_size) {
	while(_buckets[++_minOccupied].isEmpty()) {};
      } else {
	_minOccupied=_bucketCnt;
      }
    }
    return res;
  }

private:
  size_t _bucketCnt;
  Stack<T>* _buckets;

  size_t _size;
  size_t _minOccupied;
};

};

#endif /* __BucketSorter__ */

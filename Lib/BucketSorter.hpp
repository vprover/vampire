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
 * @file BucketSorter.hpp
 * Defines class BucketSorter.
 */


#ifndef __BucketSorter__
#define __BucketSorter__

#include "Stack.hpp"

namespace Lib {

/**
 * Object that distributes objects into buckets (their number specified
 * in the constructor) based on the result of the @b Evaluator::eval
 * function, and then allows retrieval of the last inserted object
 * from the smallest bucket
 *
 * @tparam T specifies the contained type.
 *
 * @tparam Evaluator must contain a function
 * static size_t eval(const T&)
 */
template<typename T, class Evaluator>
class BucketSorter
{
public:
  /**
   * Create a @b BucketSorter object that is able to contain buckets less
   * than @b bucketCnt
   */
  BucketSorter(size_t bucketCnt)
  : _bucketCnt(bucketCnt), _size(0), _minOccupied(bucketCnt)
  {
    CALL("BucketSorter::BucketSorter");

    _buckets=static_cast<Stack<T>*>(ALLOC_KNOWN(_bucketCnt*sizeof(Stack<T>), "BucketSorter"));
    for(unsigned i=0;i<_bucketCnt;i++) {
      new (&_buckets[i]) Stack<T>(8);
    }
  }

  /** Destroy the @b BucketSorter object */
  ~BucketSorter()
  {
    CALL("BucketSorter::~BucketSorter");

    for(unsigned i=0;i<_bucketCnt;i++) {
      _buckets[i].~Stack<T>();
    }
    DEALLOC_KNOWN(_buckets, _bucketCnt*sizeof(Stack<T>), "BucketSorter");
  }

  /** Return @b true if this object contains no elements */
  inline bool isEmpty() { return _size==0; }

  /** Insert an element @b obj into this object */
  void insert(T obj)
  {
    CALL("BucketSorter::insert");

    _size++;
    size_t i=Evaluator::eval(obj);
    _buckets[i].push(obj);
    if(i<_minOccupied) {
      _minOccupied=i;
    }
  }

  /** Remove the last inserted element from the smallest bucket and return it */
  T pop()
  {
    CALL("BucketSorter::pop");
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
  /** Number of buckets in the object */
  size_t _bucketCnt;
  /** Array of stacks, each of which represents one bucket */
  Stack<T>* _buckets;

  /** Number of elements stored in this object */
  size_t _size;
  /** The smallest index of a bucket that contains an element, or @b _bucketCnt
   * if the object is empty */
  size_t _minOccupied;
};

};

#endif /* __BucketSorter__ */

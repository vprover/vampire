/**
 * @file BinaryHeap.hpp
 * Defines class BinaryHeap<T, Comparator> of binary heaps.
 */

#ifndef __BinaryHeap__
#define __BinaryHeap__

#include <algorithm>

#include "../Debug/Assertion.hpp"
#include "Allocator.hpp"
#include "Exception.hpp"
#include "Comparison.hpp"

namespace Lib {

/**
 * Class BinaryHeap implements a binary minimum heap using an array which expands,
 * when additional space is needed..
 *
 * @param T a type, that will be contained in the BinaryHeap object
 * @param Comparator class, that contains a static method, that can be
 * 	called as Comparator::compare(a, b), where a and b are of type T,
 * 	and returns Lib::Comparison enumeration member.
 */
template <typename T, class Comparator>
class BinaryHeap
{
public:
  /** Create a new BinaryHeap */
  BinaryHeap()
  : _size(0), _capacity(0), _data(0), _data1(0)
  {
  }

  /** Deallocate the BinaryHeap */
  ~BinaryHeap()
  {
    CALL("BinaryHeap::~BinaryHeap");
    if(_data) {
      T* ep=_data+_capacity;
      while(ep!=_data1) {
	(--ep)->~T();
      }
      DEALLOC_KNOWN(_data,_capacity*sizeof(T),"BinaryHeap::T");
    }
  }


  /** Return mumber of items stored in this BinaryHeap */
  inline
  int size() const
  {
    ASS(_size>=0);
    return _size;
  }

  /** Return true, iff there are no items in the heap */
  inline
  bool isEmpty() const
  {
    ASS(_size>=0);
    return _size==0;
  }

  /** Insert an item to the heap */
  inline
  void insert(T obj)
  {
    CALL("BinaryHeap::insert");
    ensureAvaiablePosition();
    _size++;
    _data1[_size]=obj;
    bubbleUp(_size);
  }

  /** Return a const reference to the smallest item in the heap */
  inline
  const T& top()
  {
    ASS(!isEmpty());
    return _data[0];
  }

  /** Remove the smallest item in the heap and return it */
  inline
  T pop()
  {
    CALL("BinaryHeap::pop");
    ASS(!isEmpty());
    T res=_data[0];
    _size--;
    if(_size) {
      std::swap(_data[0],_data[_size]);
      bubbleDown(1);
    }

    //this will cause the content of removed item to be destroyed
    //and an empty item to be put at its position
    _data[_size].~T();
    new(&_data[_size]) T();

    return res;
  }

private:
  /** Copy constructor is private and without a body, because we don't want any. */
  BinaryHeap(const BinaryHeap& obj);
  /** operator= is private and without a body, because we don't want any. */
  BinaryHeap& operator=(const BinaryHeap& obj);

  /** Check whether the heap property holds between the element at @index and its ancestors */
  void bubbleUp(int index)
  {
    CALL("BinaryHeap::bubbleUp");
    ASS(index>0 && index<=_size);
    int nextIndex=index>>1;
    while(nextIndex) {
      if(Comparator::compare(_data1[index], _data1[nextIndex])==LESS) {
	std::swap(_data1[index], _data1[nextIndex]);
      } else {
	return;
      }
      index=nextIndex;
      nextIndex=index>>1;
    }
  }

  /** Check whether the heap property holds between the element at @index and its descendants */
  void bubbleDown(int index)
  {
    CALL("BinaryHeap::bubbleDown");
    ASS(index>0 && index<=_size);
    int nextIndex=index<<1;
    while(nextIndex<=_size) {
      if(nextIndex!=_size && Comparator::compare(_data1[index], _data1[nextIndex|1])==GREATER) {
	if(Comparator::compare(_data1[nextIndex|1], _data1[nextIndex])==GREATER) {
	  std::swap(_data1[index], _data1[nextIndex]);
	} else {
	  std::swap(_data1[index], _data1[nextIndex|1]);
	  nextIndex|=1;
	}
      } else if(Comparator::compare(_data1[index], _data1[nextIndex])==GREATER) {
	std::swap(_data1[index], _data1[nextIndex]);
      }
      index=nextIndex;
      nextIndex=index<<1;
    }
  }

  /** Ensure there is at least one unused position at the end of _data array */
  inline
  void ensureAvaiablePosition()
  {
    ASS(_capacity>=_size);
    if(_capacity==_size)
      expand();
  }

  /**
   * Expand BinaryHeap to double of its current size.
   *
   * Should be called only when _capacity==_size.
   */
  void expand()
  {
    CALL("BinaryHeap::expand");

    ASS(_capacity==_size);

    int oldCapacity=_capacity;
    T* oldData=_data;

    _capacity= _capacity ? _capacity*2 : 4;

    void* mem = ALLOC_KNOWN(_capacity*sizeof(T),"BinaryHeap::T");
    _data = new(mem) T [_capacity];
    _data1 = _data-1;

    if(_size) {
      T* otp = oldData+_size;
      T* ntp = _data+_size;
      do {
	*(--ntp)=*(--otp);
	//because oldCapacity==_size, we destroy all elements of oldData array here
	otp->~T();
      } while(ntp!=_data);
    }

    if(oldData) {
      DEALLOC_KNOWN(oldData,oldCapacity*sizeof(T),"BinaryHeap::T");
    }
  }

  /** Number of entries stored in this BinaryHeap */
  int _size;
  /** Size of the _data array */
  int _capacity;

  /** Array containing the heap tree */
  T* _data;

  /**
   * Pointer to the T before the start of the _data
   * (we can use it for one-based access to _data)
   */
  T* _data1;

}; // class BinaryHeap

};

#endif // __BinaryHeap__



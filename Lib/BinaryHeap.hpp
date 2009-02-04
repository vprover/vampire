/**
 * @file BinaryHeap.hpp
 * Defines class BinaryHeap<T, Comparator> of binary heaps.
 */

#ifndef __BinaryHeap__
#define __BinaryHeap__

#include <algorithm>
#include <limits>

#include "../Debug/Assertion.hpp"
#include "Allocator.hpp"
#include "Exception.hpp"
#include "Comparison.hpp"
#include "BacktrackData.hpp"

namespace Lib {

/**
 * Class BinaryHeap implements a binary minimum heap using an array which expands,
 * when additional space is needed..
 *
 * @param T a type, that will be contained in the BinaryHeap object
 * @param Comparator class, that contains a static method, that can be
 * 	called as Comparator::compare(a, b), where a and b are of type T,
 * 	and returns Lib::Comparison enumeration member. Also, in order to
 * 	use backtrackable insert, Comparator should contain static method
 * 	max() that returns object T such that all other objects T are
 * 	smaller.
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
      T* ep=_data+_size;
      while(ep!=_data1) {
	(--ep)->~T();
      }
      DEALLOC_KNOWN(_data,_capacity*sizeof(T),"BinaryHeap::T");
    }
  }

  void reset()
  {
    T* ep=_data+_size;
    while(ep!=_data1) {
	(--ep)->~T();
    }
    _size=0;
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
    new(&_data1[_size]) T(obj);
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
    _data[_size].~T();
    return res;
  }

  T backtrackablePop(BacktrackData& bd)
  {
    CALL("BinaryHeap::backtrackablePop");
    ASS(!isEmpty());
    T res=_data[0];
    _size--;
    if(_size) {
      std::swap(_data[0],_data[_size]);
      int lastBubbleIndex=bubbleDown(1);
      bd.addBacktrackObject(
  	    new BHPopBacktrackObject(this, res, lastBubbleIndex));
    } else {
      bd.addBacktrackObject(
  	    new BHPopBacktrackObject(this, res, 1));
    }
    _data[_size].~T();
    return res;
  }
  void backtrackableInsert(T obj, BacktrackData& bd)
  {
    CALL("BinaryHeap::backtrackableInsert");
    ensureAvaiablePosition();
    _size++;
    new(&_data1[_size]) T(obj);
    int lastBubbleIndex=bubbleUp(_size);
    bd.addBacktrackObject(
	    new BHInsertBacktrackObject(this, lastBubbleIndex));
  }


private:
  class BHPopBacktrackObject
  : public BacktrackObject
  {
  public:
    BHPopBacktrackObject(BinaryHeap* bh, T v, int lastBubbleIndex)
    :_bh(bh), _val(v), _lastBubbleIndex(lastBubbleIndex) {}
    void backtrack()
    {
      //During insertion, the first item is swapped with the last,
      //removed from the end of the array, and then the item at
      //the first position bubbles down, until the heap condition
      //is fulfilled. Here we reverse the process provided that
      //_lastBubbleIndex is the current index of the formerly last
      //element.
      _bh->_size++;
      new(&_bh->_data1[_bh->_size]) T(_val);
      std::swap(_bh->_data1[_bh->_size], _bh->_data1[_lastBubbleIndex]);
      //Now at the position _lastBubbleIndex is the smallest element
      //of the heap, so we know that it will bubble up to the first
      //position[1]. (There's only one way to do that, so the heap will
      //be exactly the same as before the popping occured.)
      //
      //[1] or, to be precise, to such position, that all elements
      //above will be equal to it.
      _bh->bubbleUp(_lastBubbleIndex);
    }
    CLASS_NAME("BinaryHeap::BHPopBacktrackObject");
    USE_ALLOCATOR(BHPopBacktrackObject);
  private:
    BinaryHeap* _bh;
    T _val;
    int _lastBubbleIndex;
  };

  class BHInsertBacktrackObject
  : public BacktrackObject
  {
  public:
    BHInsertBacktrackObject(BinaryHeap* bh, int lastBubbleIndex)
    :_bh(bh), _lastBubbleIndex(lastBubbleIndex) {}
    void backtrack()
    {
      //We replace the inserted element with maximal possible
      //element, so that we know for sure, that when we do
      //bubbleDown() on it, a maximal element will be at the
      //last position. Also from the way how bubbleDown works
      //we know, that the heap will be exactly the same as before
      //inserting.
      _bh->_data1[_lastBubbleIndex]=Comparator::max();
      _bh->bubbleDown(_lastBubbleIndex);
      ASS(_bh->_data1[_bh->_size]==Comparator::max());
      _bh->_data1[_bh->_size].~T();
      _bh->_size--;
    }
    CLASS_NAME("BinaryHeap::BHInsertBacktrackObject");
    USE_ALLOCATOR(BHInsertBacktrackObject);
  private:
    BinaryHeap* _bh;
    int _lastBubbleIndex;
  };

  /** Copy constructor is private and without a body, because we don't want any. */
  BinaryHeap(const BinaryHeap& obj);
  /** operator= is private and without a body, because we don't want any. */
  BinaryHeap& operator=(const BinaryHeap& obj);

  /** Make sure the heap property is not violated by the element
   * at @b index wrt its ancestors, and return its new index. */
  int bubbleUp(int index)
  {
    CALL("BinaryHeap::bubbleUp");
    ASS(index>0 && index<=_size);
    int nextIndex=index>>1;
    while(nextIndex) {
      if(Comparator::compare(_data1[index], _data1[nextIndex])==LESS) {
	std::swap(_data1[index], _data1[nextIndex]);
      } else {
	return index;
      }
      index=nextIndex;
      nextIndex=index>>1;
    }
    return 1;
  }

  /** Make sure the heap property is not violated by the element
   * at @b index wrt its descendants, and return its new index. */
  int bubbleDown(int index)
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
      } else {
	return index;
      }
      index=nextIndex;
      nextIndex=index<<1;
    }
    return index;
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
    _data = static_cast<T*>(mem);
    _data1 = _data-1;

    if(_size) {
      T* otp = oldData+_size;
      T* ntp = _data+_size;
      do {
	new(--ntp) T(*(--otp));
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



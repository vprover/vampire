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
 * @file DynamicHeap.hpp
 * Defines class DynamicHeap.
 */

#ifndef __DynamicHeap__
#define __DynamicHeap__

#include <algorithm>

#include "Forwards.hpp"

#include "Debug/Assertion.hpp"

#include "Comparison.hpp"
#include "DArray.hpp"
#include "DHMap.hpp"

namespace Lib {

using namespace std;

/**
 * Minimum binary heap
 */
template<class T, class Comparator, class ElMap = DHMap<T,size_t>, class TArg = T >
class DynamicHeap {
public:
  DynamicHeap(Comparator cmp=Comparator()) : _heap(0), _cmp(cmp) {}

  /**
   * Add @c obj to the end of the heap 
   * (heap property not being maintained).
   *
   * An object can appear in the heap at most once.
   */
  void addToEnd(TArg obj)
  {
    CALL("DynamicHeap::addToEnd");
    ASS(!contains(obj));

    size_t newIdx1 = size()+1;
    _heap.expand(newIdx1);
    getData1()[newIdx1] = obj;
    _elMap.insert(obj, newIdx1);    
  }  

  /**
   * Restore heap property (after a series of addToEnd calls
   * and/or un-notified Increases/Decreases)
   */  
  void heapify()
  {
    CALL("DynamicHeap::heapify");
        
    for (size_t i = (size() >> 1); i > 0; i--) {
      fixIncrease1(i);
    }
  }
  
  /**
   * Insert @c obj into the heap
   *
   * An object can appear in the heap at most once.
   */
  void insert(TArg obj)
  {
    CALL("DynamicHeap::insert");
    
    addToEnd(obj);
    size_t newIdx1 = size();
    fixDecrease1(newIdx1);
  }
  
  T pop()
  {
    CALL("DynamicHeap::pop");
    T res = _heap[0];

    T* data1 = getData1();
    size_t backIdx1 = size();
    data1[1] = data1[backIdx1];
    _heap.expand(backIdx1-1);
    _elMap.remove(res);

    if(backIdx1!=1) {
      //we still have some elements left
      _elMap.set(data1[1], 1);
      fixIncrease1(1);
    }

    return res;
  }

  void notifyIncrease(TArg obj)
  {
    CALL("DynamicHeap::notifyIncrease");
    
    size_t idx = _elMap.get(obj);
    ASS(idx==1 || !isGreater1(idx/2, idx)); //check that we didn't decrease
    fixIncrease1(idx);
  }

  void notifyDecrease(TArg obj)
  {
    CALL("DynamicHeap::notifyDecrease");

    size_t idx = _elMap.get(obj);
    ASS(idx*2>size() || !isGreater1(idx, idx*2)); //check that we didn't increase
    ASS(idx*2+1>size() || !isGreater1(idx, idx*2+1)); //check that we didn't increase
    fixDecrease1(idx);
  }

  TArg top() const
  {
    CALL("DynamicHeap::insert");
    ASS(!isEmpty());

    return _heap[0];
  }

  bool contains(TArg obj)
  {
    CALL("DynamicHeap::contains");

    return _elMap.find(obj);
  }

  size_t size() const { return _heap.size(); }

  bool isEmpty() const { return size()==0; }

  ElMap& elMap() { return _elMap; }
private:
  //'1' appended to a function name means that it receives one-based indexes as arguments


  /**
   * Fix decrease of element at one-based index @c idx1.
   */
  void fixDecrease1(size_t idx)
  {
    CALL("DynamicHeap::fixDecrease1");
    ASS_G(idx, 0);
    ASS_LE(idx, size());

    while(idx>1) {
      size_t parent = idx/2;
      if(!isGreater1(parent, idx)) {
	break;
      }
      swapInHeap1(idx, parent);
      idx = parent;
    }
  }

  /**
   * Fix increase of element at one-based index @c idx.
   */
  void fixIncrease1(size_t idx)
  {
    CALL("DynamicHeap::fixDecrease1");
    ASS_G(idx, 0);
    ASS_LE(idx, size());

    size_t maxIdx = size();

    for(;;) {
      size_t child1 = idx*2;
      if(child1>maxIdx) {
	break;
      }
      if(child1==maxIdx) {
	if(isGreater1(idx, child1)) {
	  swapInHeap1(idx, child1);
	}
	break;
      }

      size_t child2 = child1+1;
      if(isGreater1(idx, child1)) {
	if(isGreater1(child1, child2)) {
	  swapInHeap1(idx, child2);
	  idx = child2;
	}
	else {
	  swapInHeap1(idx, child1);
	  idx = child1;
	}
      }
      else if(isGreater1(idx, child2)) {
	swapInHeap1(idx, child2);
	idx = child2;
      }
      else {
	break;
      }
    }
  }

  /**
   * Return true if element at one-based index @c idxA is greater than
   * the one at @c idxB
   */
  bool isGreater1(size_t idxA, size_t idxB)
  {
    CALL("DynamicHeap::isGreater1");
    ASS_G(idxA, 0);
    ASS_LE(idxA, size());
    ASS_G(idxB, 0);
    ASS_LE(idxB, size());

    T* data1 = getData1();
    return _cmp.compare(data1[idxA], data1[idxB])==GREATER;
  }

  /**
   * Swap elements at one-based indexes @c idxA and @c idxB.
   */
  void swapInHeap1(size_t idxA, size_t idxB)
  {
    CALL("DynamicHeap::swapInHeap1");

    T* data1 = getData1();
    swap(data1[idxA], data1[idxB]);
    _elMap.set(data1[idxA], idxA);
    _elMap.set(data1[idxB], idxB);
  }

  /**
   * Return pointer to heap data that can be accessed as an one-based array
   */
  T* getData1() { return _heap.array()-1; }

  DArray<T> _heap;
  /**
   * Maps elements to their position in the heap
   */
  ElMap _elMap;

  Comparator _cmp;
};

}

#endif // __DynamicHeap__

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
 * @file PairUtils.hpp
 * Defines class PairUtils.
 */


#ifndef __PairUtils__
#define __PairUtils__

#include "Metaiterators.hpp"
#include "Metaarrays.hpp"

namespace Lib {

template<typename P>
struct FirstOfPairFn
{
  typename P::first_type operator()(P p) { return p.first; }
};

template<typename P>
struct SecondOfPairFn
{
  typename P::second_type operator()(P p) { return p.second; }
};

template<typename C, typename D>
struct PairRightPushingFn
{
  PairRightPushingFn(C c) : _c(c) {}
  pair<C,D> operator()(D d) { return pair<C,D>(_c,d); }
private:
  C _c;
};

template<typename C, class D>
struct PairLeftPushingFn
{
  PairLeftPushingFn(D d): _d(d) {}
  pair<C,D> operator()(C c) { return pair<C,D>(c,_d); }
private:
  D _d;
};


///@addtogroup Iterators
///@{

/**
 * Given pair of an object A and an iterator I, return
 * an iterator J, that yields pairs (A,C), where C are
 * objects returned by iterator I. This virtually pushes
 * the pair structure into the iterator I.
 */
template<typename C, typename DIt>
MappingIterator<DIt,PairRightPushingFn<C,ELEMENT_TYPE(DIt)> >
  pushPairIntoRightIterator(pair<C, DIt > obj)
{
  return getMappingIterator(obj.second, PairRightPushingFn<C,ELEMENT_TYPE(DIt)>(obj.first));
}

template<typename C, typename DIt>
MappingIterator<DIt,PairRightPushingFn<C,ELEMENT_TYPE(DIt)> >
  pushPairIntoRightIterator(C c, DIt dit)
{
  return getMappingIterator(dit, PairRightPushingFn<C,ELEMENT_TYPE(DIt)>(c));
}

template<typename C, typename D>
class RightPushedPair
{
public:
  DECL_ELEMENT_TYPE(pair<C,ELEMENT_TYPE(D)>);
  DECL_ITERATOR_TYPE(MappingIterator<ITERATOR_TYPE(D),PairRightPushingFn<C,ELEMENT_TYPE(D)> >);
  RightPushedPair(pair<C,D> p) : _p(p) {}
  pair<C,D> get() { return _p; }
private:
  pair<C,D> _p;
};

/**
 * Given pair of an object A and an iterable object B, return
 * an iterable object, that contains pairs (A,C), where C are
 * objects from B. So this virtually pushes the pair structure
 * into the iterable object B.
 */
template<typename C, typename D>
RightPushedPair<C,D> pushPairIntoRightIterable(pair<C, D> obj)
{
  return RightPushedPair<C,D>(obj);
}

template<typename C, typename D>
struct PushPairIntoRightIterableFn
{
  RightPushedPair<C,D> operator()(pair<C, D> obj)
  {
    return pushPairIntoRightIterable(obj);
  }
};

/** See VirtualIterator.hpp */
template<typename C, typename DItb>
MappingIterator<ITERATOR_TYPE(DItb),PairRightPushingFn<C,ELEMENT_TYPE(DItb)> >
  getContentIterator(RightPushedPair<C,DItb> obj)
{
  return pushPairIntoRightIterator(obj.get().first,
	  getContentIterator(obj.get().second) );
}

///@}


template<typename C, class Arr>
MappingArray<Arr,PairRightPushingFn<C,ELEMENT_TYPE(Arr)> >
pushPairIntoRightArray(pair<C,Arr> p)
{
  return getMappingArray(p.second, PairRightPushingFn<C,ELEMENT_TYPE(Arr)>(p.first));
}

template<class Arr, typename D>
MappingArray<Arr,PairLeftPushingFn<ELEMENT_TYPE(Arr),D> >
pushPairIntoLeftArray(pair<Arr,D> p)
{
  return getMappingArray(p.first, PairLeftPushingFn<ELEMENT_TYPE(Arr),D>(p.second));
}
template<class Arr, typename D>
MappingArray<Arr,PairLeftPushingFn<ELEMENT_TYPE(Arr),D> >
pushPairIntoLeftArray(Arr arr, D d)
{
  return getMappingArray(arr, PairLeftPushingFn<ELEMENT_TYPE(Arr),D>(d));
}


/**
 * Array of pairs, created from a pair of arrays of equal size.
 */
template<class Arr1, class Arr2>
class PairsPushingArray
{
public:
  DECL_ELEMENT_TYPE( pair<ELEMENT_TYPE(Arr1), ELEMENT_TYPE(Arr2)> );
//  typedef pair<typename Arr1::OWN_ELEMENT_TYPE,typename Arr2::OWN_ELEMENT_TYPE> OWN_ELEMENT_TYPE;

  explicit PairsPushingArray(pair<Arr1,Arr2> p)
  : _arr1(p.first), _arr2(p.second) {}

  template<typename Idx>
  OWN_ELEMENT_TYPE operator[] (Idx index)
  {
    return OWN_ELEMENT_TYPE(_arr1[index], _arr2[index]);
  }
  size_t size()
  {
    ASS(_arr1.size()==_arr2.size());
    return _arr1.size();
  }
private:
  Arr1 _arr1;
  Arr2 _arr2;
};

template<class Arr1, class Arr2>
PairsPushingArray<Arr1,Arr2> pushPairIntoArrays(pair<Arr1,Arr2> p)
{
  return PairsPushingArray<Arr1,Arr2>(p);
}

template<class Arr1, class Arr2>
PairsPushingArray<Arr1,Arr2> pushPairIntoArrays(Arr1 arr1,Arr2 arr2)
{
  return PairsPushingArray<Arr1,Arr2>(pair<Arr1,Arr2>(arr1,arr2));
}


};

#endif /* __PairUtils__ */

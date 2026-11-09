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
  std::pair<C,D> operator()(D d) { return std::pair<C,D>(_c,d); }
private:
  C _c;
};

template<typename C, class D>
struct PairLeftPushingFn
{
  PairLeftPushingFn(D d): _d(d) {}
  std::pair<C,D> operator()(C c) { return std::pair<C,D>(c,_d); }
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
MappingIterator<DIt,PairRightPushingFn<C,typename DIt::ElementType> >
  pushPairIntoRightIterator(std::pair<C, DIt > obj)
{
  return getMappingIterator(obj.second, PairRightPushingFn<C,typename DIt::ElementType>(obj.first));
}

template<typename C, typename DIt>
MappingIterator<DIt,PairRightPushingFn<C,typename DIt::ElementType> >
  pushPairIntoRightIterator(C c, DIt dit)
{
  return getMappingIterator(std::move(dit), PairRightPushingFn<C,typename DIt::ElementType>(c));
}

///@}

};

#endif /* __PairUtils__ */

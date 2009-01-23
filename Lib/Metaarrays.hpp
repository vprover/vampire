/**
 * @file Metaarrays.hpp
 * Defines class Metaarrays.
 */


#ifndef __Metaarrays__
#define __Metaarrays__

#include "../Forwards.hpp"

#include "VirtualIterator.hpp"

namespace Lib {

/**
 * Provides constant-time copyable wrapper for an array.
 *
 * Useful eg. when DArray should take part in a std::pair
 * structure, that will be passed as parameter to some template
 * method, that requires an array object, not just pointer to it.
 */
template<class Arr>
class ReferencedArrayWrapper
{
public:
  DECL_ELEMENT_TYPE( ELEMENT_TYPE(Arr) );
  explicit ReferencedArrayWrapper(Arr& a) : _a(a) {}
  ///Return @b index-th element of the wrapped array
  template<typename Idx>
  OWN_ELEMENT_TYPE operator[] (Idx index) { return _a[index]; }
  ///Return size of the wrapped array
  size_t size() {return _a.size(); }
private:
  Arr& _a;
};

/**
 * Method, that wraps an array object into constant-time
 * copyable wrapper.
 * @see ReferencedArrayWrapper
 */
template<class Arr>
ReferencedArrayWrapper<Arr> wrapReferencedArray(Arr& a)
{
  return ReferencedArrayWrapper<Arr>(a);
}


template<class Arr, typename Functor>
class MappingArray
{
public:
  explicit MappingArray(Arr arr, Functor func)
  : _arr(arr), _func(func) {}

  template<typename Idx>
  RETURN_TYPE(Functor) operator[] (Idx index) { return _func(_arr[index]); }
  size_t size() {return _arr.size(); }
private:
  Arr _arr;
  Functor _func;
};

template<class Arr, typename Functor>
MappingArray<Arr,Functor> getMappingArray(Arr arr, Functor func)
{
  return MappingArray<Arr,Functor>(arr, func);
}


//template<typename C, class Arr>
//class PairRightPushingArray
//{
//public:
//  DECL_ELEMENT_TYPE( pair<C,ELEMENT_TYPE(Arr)> );
////  typedef pair<C,typename Arr::OWN_ELEMENT_TYPE> OWN_ELEMENT_TYPE;
//
//  explicit PairRightPushingArray(pair<C,Arr> p)
//  : _c(p.first), _arr(p.second) {}
//
//  template<typename Idx>
//  OWN_ELEMENT_TYPE operator[] (Idx index)
//  {
//    return OWN_ELEMENT_TYPE(_c, _arr[index]);
//  }
//  size_t size() {return _arr.size(); }
//private:
//  C _c;
//  Arr _arr;
//};

template<typename C, class D>
struct PairRightPushingAuxFunctor
{
  DECL_RETURN_TYPE(pair<C,D>);
  PairRightPushingAuxFunctor(C c): _c(c) {}
  OWN_RETURN_TYPE operator()(D d)
  { return pair<C,D>(_c,d); }
private:
  C _c;
};

template<typename C, class Arr>
MappingArray<Arr,PairRightPushingAuxFunctor<C,ELEMENT_TYPE(Arr)> >
pushPairIntoRightArray(pair<C,Arr> p)
{
//  return PairRightPushingArray<C,Arr>(p);
  return getMappingArray(p.second, PairRightPushingAuxFunctor<C,ELEMENT_TYPE(Arr)>(p.first));
}

template<typename C, class D>
struct PairLeftPushingAuxFunctor
{
  DECL_RETURN_TYPE(pair<C,D>);
  PairLeftPushingAuxFunctor(D d): _d(d) {}
  OWN_RETURN_TYPE operator()(C c)
  { return pair<C,D>(c,_d); }
private:
  D _d;
};

template<class Arr, typename D>
MappingArray<Arr,PairLeftPushingAuxFunctor<ELEMENT_TYPE(Arr),D> >
pushPairIntoLeftArray(pair<Arr,D> p)
{
  return getMappingArray(p.first, PairLeftPushingAuxFunctor<ELEMENT_TYPE(Arr),D>(p.second));
}
template<class Arr, typename D>
MappingArray<Arr,PairLeftPushingAuxFunctor<ELEMENT_TYPE(Arr),D> >
pushPairIntoLeftArray(Arr arr, D d)
{
  return getMappingArray(arr, PairLeftPushingAuxFunctor<ELEMENT_TYPE(Arr),D>(d));
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

#endif /* __Metaarrays__ */

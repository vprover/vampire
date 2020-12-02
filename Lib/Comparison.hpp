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
 * @file Comparison.hpp
 * Defines the Compare enum
 * @since 25/12/2003 Manchester
 */

#ifndef __VL_COMPARE__
#define __VL_COMPARE__


namespace Lib {

/**
 * Type denoting the result of comparison.
 */
enum Comparison
{
  LESS = -1,
  EQUAL = 0,
  GREATER = 1
};

/**
 * Type denoting the result of comparison of simplification orderings.
 * @since 25/03/2007 Manchester
 */
enum PartialComparison
{
  PC_LESS = -1,
  PC_EQUAL = 0,
  PC_GREATER = 1,
  PC_INCOMPARABLE = 2
};

//
// It's a bit messy here since we have two kinds of cmparators:
// One kind has the compare() function as static and the other not.
// This leads to two having two kinds of meta-comparators. We should
// probably eventually get rid of the static comparators, to make the
// code more consistent.
//
struct DefaultComparatorTKV
{
  template<typename T>
  inline static Comparison compare(T o1, T o2)
  {
    return o1>o2 ? GREATER : (o1==o2 ? EQUAL : LESS);
  }
};


template<class Comp>
struct ReversedComparator
{
  template<typename T>
  inline static Comparison compare(T o1, T o2)
  {
    return static_cast<Comparison>(-Comp::compare(o1, o2));
  }
};

template<class Comp1, class Comp2>
class CompositeComaprator
{
public:
  CompositeComaprator(Comp1 c1=Comp1(), Comp2 c2=Comp2())
  : _c1(c1), _c2(c2) {}

  template<typename T>
  Comparison compare(T o1, T o2)
  {
    Comparison res1=_c1.compare(o1,o2);
    return (res1==EQUAL) ? _c2.compare(o1,o2) : res1;
  }
private:
  Comp1 _c1;
  Comp2 _c2;
};

template<class Closure> 
class ClosureComparator
{
  Closure _self;
public:
  ClosureComparator(Closure self) : _self(self) {}

  template<typename T>
  Comparison compare(T l, T r) const& { return _self(l,r); }
};

template<class Closure>
inline ClosureComparator<Closure> closureComparator(Closure c) 
{
  return ClosureComparator<Closure>(c);
}

//struct DefaultComparator
//{
//  template<typename T>
//  Comparison compare(T o1, T o2)
//  {
//    if(o1==o2) {
//      return EQUAL;
//    }
//    else if(o1<o2) {
//      return LESS;
//    }
//    else {
//      ASS(o1>o2);
//      return GREATER;
//    }
//  }
//};


}

#endif

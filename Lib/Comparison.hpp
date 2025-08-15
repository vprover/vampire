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

#include <utility>

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

inline Comparison revert(Comparison c) { return static_cast<Comparison>(-c); }

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

template<class F, class... Fs>
Comparison lexCompare(Comparison c, F f, Fs... fs) 
{ return c != EQUAL ? c : lexCompare(f(), std::move(fs)...); }

inline Comparison lexCompare(Comparison c)
{ return c; }

}

#endif

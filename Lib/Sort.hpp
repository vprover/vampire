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
 * @file Sort.hpp
 *
 * @since 06/05/2002
 * @since 16/07/2003 flight Moscow-London, changed from a
 *   previous single-type version.
 */


#ifndef __Sort__
#define __Sort__

#include "Comparison.hpp"
#include "Debug/Assertion.hpp"

namespace Lib {

/** A type level predicate that tells whether there is a function `Result T::compare(T const&) const;` for some result type Result. o
 * It provides the bool constexpr `HasCompareFunction<T>::value`
 */
template<class T>
struct HasCompareFunction 
{ 
  template<class U> 
  static constexpr decltype(std::declval<U const&>().compare(std::declval<U const&>()), bool()) check(int) { return true; }

  template<class U> static constexpr bool check(...) { return false; }

  static constexpr bool value = check<T>(int(0)); 
};


struct DefaultComparator
{

  static Comparison compare(unsigned a, unsigned b)
  { return a == b ? EQUAL : a < b ? LESS : GREATER; }

  template<typename T>
  static typename std::enable_if<
    HasCompareFunction<T>::value,
    Comparison
  >::type 
  compare(T const& lhs, T const& rhs)
  { return lhs.compare(rhs); }


  template<typename T>
  static typename std::enable_if<
    !HasCompareFunction<T>::value,
    Comparison
  >::type 
  compare(T const& a, T const& b)
  {
    ASS(a < b || b < a || a == b)
    return a < b ? LESS 
         : b < a ? GREATER 
         : EQUAL;
  }
};

} // namespace Lib

#endif



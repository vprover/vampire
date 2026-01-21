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
 * Various functions on integers that should probably
 * have been included in a C++ standard library.
 * @since 06/08/1999 Uppsala
 * @since 19/02/2000 Manchester, slightly reimplemented
 * @since 09/06/2000 Manchester, toString added and int.cpp created
 */

#ifndef __INT__
#define __INT__

#include "Comparison.hpp"

#include <string>

namespace Lib {

/**
 * Various functions on integers that should probably
 * have been included in a C++ standard library.
 */
class Int
{
 public:
  static std::string toString(int i);
  static std::string toString(unsigned i);
  static std::string toString(unsigned long i);
  static std::string toString(long l);
  /** Return the std::string representation of a float */
  static std::string toString(float f) { return toString((double)f); }
  static std::string toString(double d);

  /** Compare two integers. */
  inline static Comparison compare (int i1, int i2)
  { return i1 < i2 ? LESS : i1 == i2 ? EQUAL : GREATER; }
  /** Compare two unsigned integers */
  inline static Comparison compare (unsigned i1, unsigned i2)
  { return i1 < i2 ? LESS : i1 == i2 ? EQUAL : GREATER; }
  /** Compare two long integers */
  inline static Comparison compare (long i1, long i2)
  { return i1 < i2 ? LESS : i1 == i2 ? EQUAL : GREATER; }
  /** Compare two unsigned long integers */
  inline static Comparison compare (unsigned long i1, unsigned long i2)
  { return i1 < i2 ? LESS : i1 == i2 ? EQUAL : GREATER; }
  /** Compare two pointers */
  inline static Comparison compare (const void* p1, const void* p2)
  { return p1 < p2 ? LESS : p1 == p2 ? EQUAL : GREATER; }
  /** Compare two floats */
  inline static Comparison compare (float f1, float f2)
  { return f1 < f2 ? LESS : f1 == f2 ? EQUAL : GREATER; }
  /** Compare two doubles */
  inline static Comparison compare (double f1, double f2)
  { return f1 < f2 ? LESS : f1 == f2 ? EQUAL : GREATER; }
  static bool stringToLong(const char*,long& result);
  static bool stringToUnsignedLong(const char*,unsigned long& result);
  static bool stringToLong(const std::string& str,long& result) {
    return stringToLong(str.c_str(),result);
  }
  static bool stringToInt(const std::string& str,int& result);
  static bool stringToInt(const char* str,int& result);
  static bool stringToUnsignedInt(const char* str,unsigned& result);
  static bool stringToUnsignedInt(const std::string& str,unsigned& result);
  static bool stringToDouble(const char*,double& result);
  static bool stringToDouble(const std::string& str,double& result) { return stringToDouble(str.c_str(), result); }
  static bool stringToFloat(const char*,float& result);
  static bool stringToUnsigned64(const std::string& str,long long unsigned& result);
  static bool stringToUnsigned64(const char* str,long long unsigned& result);
};

template <typename T>
using disable_deduction = typename std::enable_if_t<true, T>;  // C++20: can use std::type_identity_t instead of this

/**
 * Check if an addition operation overflows.
 * - This check is very sensitive to using the correct type,
 *   and implicit conversions in C++ may easily destroy it
 *   and lead to unexpected results.
 *   For this reason, the type parameter should be given explicitly.
 * - Wrap-around behaviour on overflow is only defined for
 *   unsigned integer types in C++.
 */
template <typename T>
inline bool isAdditionOverflow(disable_deduction<T> a, disable_deduction<T> b)
{
  static_assert(std::is_unsigned<T>::value, "overflow check is only defined for unsigned types");
  return static_cast<T>(a + b) < a;
}

}

#endif  // __INT__


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
#include "Portability.hpp"
#include "VString.hpp"

#include <iostream>

using namespace std;

#ifdef _MSC_VER // VC++
#  undef max
#  undef min
#endif

namespace Lib {


/**
 * Various functions on integers that should probably
 * have been included in a C++ standard library.
 */
class Int
{
 public:
  static vstring toString(int i);
  static vstring toString(unsigned i);
  static vstring toString(unsigned long i);
  static vstring toString(long l);
  /** Return the vstring representation of a float */
  static vstring toString(float f) { return toString((double)f); }
  static vstring toString(double d);

  static vstring toHexString(size_t i);

	static bool isInteger(const char* str);
	/** True if @b str is a string representing an (arbitrary precision) integer */
	static inline bool isInteger(const vstring& str) { return isInteger(str.c_str()); }

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
  static bool stringToLong(const vstring& str,long& result) {
    return stringToLong(str.c_str(),result);
  }
  static bool stringToInt(const vstring& str,int& result);
  static bool stringToInt(const char* str,int& result);
  static bool stringToUnsignedInt(const char* str,unsigned& result);
  static bool stringToUnsignedInt(const vstring& str,unsigned& result);
  static bool stringToDouble(const char*,double& result);
  static bool stringToDouble(const vstring& str,double& result) { return stringToDouble(str.c_str(), result); }
  static bool stringToFloat(const char*,float& result);
  static bool stringToUnsigned64(const vstring& str,long long unsigned& result);
  static bool stringToUnsigned64(const char* str,long long unsigned& result);
  static int sign(int i);
  static int sign(long i);
  static int sign(double);
  static int max(int i,int j);
  static int min(int i,int j);

  /** Return the greatest common divisor of @b i and @b j */
  template<typename INT>
  static unsigned gcd(INT i,INT j)
  {
    CALL("Int::gcd");

    unsigned a=safeAbs(i);
    unsigned b=safeAbs(j);

    if(!a && !b) {
      return 1; // gcd of (0,0) set arbitrarily to 1
    }

    while (b!=0) {
      a %= b;
      if(a==0) {
        return b;
      }
      b %= a;
    }
    return a;
  }

  /**
   * If -num does not overflow, return true and save -num to res.
   * Otherwise, return false.
   */
  template<typename INT>
  static bool safeUnaryMinus(const INT num, INT& res)
  {
    CALL("Int::safeUnaryMinus");

    if(num == numeric_limits<INT>::min()) {
      return false;
    }
    res=-num;
    return true;
  }

  static unsigned safeAbs(const int num)
  {
    CALL("Int::safeAbs");

    if(num == numeric_limits<int>::min()) { // = -2147483648
      return (unsigned)num; // = 2147483648
    }
    // abs works for all other values
    return abs(num);
  }

  /**
   * If arg1+arg2 does not overflow, return true and save the sum to res.
   * Otherwise, return false.
   */
  template<typename INT>
  static bool safePlus(INT arg1, INT arg2, INT& res)
  {
    CALL("Int::safePlus");

    if(arg2<0) {
      if(numeric_limits<INT>::min() - arg2 > arg1) { return false; }
    }
    else {
      if(numeric_limits<INT>::max() - arg2 < arg1) { return false; }
    }
    res=arg1+arg2;
    return true;
  }

  /**
   * If arg1-arg2 does not overflow, return true and save the result to res.
   * Otherwise, return false.
   */
  template<typename INT>
  static bool safeMinus(INT num, INT sub, INT& res)
  {
    CALL("Int::safeMinus");

    if(sub<0) {
      if(numeric_limits<INT>::max() + sub < num) { return false; }
    }
    else {
      if(numeric_limits<INT>::min() + sub > num) { return false; }
    }
    res=num-sub;
    return true;
  }

  template <typename T>
  static int sgn(T val) {
    CALL("Int::sgn");
    return (T(0) < val) - (val < T(0));
  }

  /**
   * If arg1*arg2 does not overflow, return true and save the result to res.
   * Otherwise, return false.
   */
  template<typename INT>
  static bool safeMultiply(INT arg1, INT arg2, INT& res)
  {
    CALL("Int::safeMultiply");

    if (arg1 == 0 || arg1 == 1 || arg2 == 0 || arg2 == 1) {
      res=arg1*arg2;
      return true;
    }

    if (arg1 == numeric_limits<INT>::min() || arg2 == numeric_limits<INT>::min()) {
      // cannot take abs of min() and all safe operations with min have been ruled out above
      return false;
    }

    // we can safely apply uminus on negative ones
    INT arg1abs = arg1 < 0 ? -arg1 : arg1;
    INT arg2abs = arg2 < 0 ? -arg2 : arg2;

    if (arg1abs > numeric_limits<INT>::max() / arg2abs) {
      return false;
    }

    INT mres = arg1*arg2;

    // this is perhaps obsolete and could be removed
    if ((mres == numeric_limits<INT>::min() && arg1 == -1) || // before, there was a SIGFPE for "-2147483648 / -1" TODO: are there other evil cases?
        (sgn(arg1)*sgn(arg2) != sgn(mres)) || // 1073741824 * 2 = -2147483648 is evil, and passes the test below
        (arg1 != 0 && mres / arg1 != arg2)) {
      return false;
    }
    res=mres;
    return true;
  }

  inline static bool safeDivide(int arg1, int arg2, int& res)
  {
    CALL("Int::safeDivide");
    if (arg2 == 0) return false;

    // check for 2 complement representation
    if (numeric_limits<int>::min() != -numeric_limits<int>::max())  {
      if (arg1 == numeric_limits<int>::min() && arg2 == -1)  {
        return false;
      }
    }
    res = arg1 / arg2;
    return true;
  }
};



/**
 * Return
 * <ol>
 *  <li>-1 if i&lt;0;</li>
 *  <li>0 if i=0;</li>
 *  <li>1 if i&gt;0.</li>
 * </ol>
 *
 * @since 22/04/2005 Manchester
 */
inline
int Int::sign(int i)
{
  return i < 0 ? -1 :
         i == 0 ? 0 :
         1;
}


/**
 * Return
 * <ol>
 *  <li>-1 if l&lt;0;</li>
 *  <li>0 if l=0;</li>
 *  <li>1 if l&gt;0.</li>
 * </ol>
 *
 * @since 22/04/2005 Manchester
 */
inline
int Int::sign(long l)
{
  return l < 0 ? -1 :
         l == 0 ? 0 :
         1;
}


/**
 * Return
 * <ol>
 *  <li>-1 if d&lt;0;</li>
 *  <li>0 if d=0;</li>
 *  <li>1 if d&gt;0.</li>
 * </ol>
 *
 * @since 22/04/2005 Manchester
 */
inline
int Int::sign(double d)
{
  return d < 0 ? -1 :
         d == 0 ? 0 :
         1;
}

/** Return the maximum of two integers */
inline
int Int::max (int i,int j)
{
  return i >= j ? i : j;
}

/** Return the minimum of two integers */
inline
int Int::min (int i,int j)
{
  return i <= j ? i : j;
}


}

#endif  // __INT__


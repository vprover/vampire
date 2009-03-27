/**
 * Various functions on integers that should probably
 * have been included in a C++ standard library.
 * @since 06/08/1999 Uppsala
 * @since 19/02/2000 Manchester, slightly reimplemented
 * @since 09/06/2000 Manchester, toString added and int.cpp created
 */

#ifndef __INT__
#define __INT__


#include <string>

#include "Comparison.hpp"
#include "Portability.hpp"

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
  static string toString(int i);
  static string toString(unsigned i);
#if ARCH_X64
  static string toString(size_t i);
#endif
  static string toString(long l);
  /** Return the string representation of a float */
  static string toString(float f) { return toString((double)f); }
  static string toString(double d);
  /** Compare two integers. */
  inline static Comparison compare (int i1, int i2)
  { return i1 < i2 ? LESS : i1 == i2 ? EQUAL : GREATER; }
  /** Compare two unsigned integers */
  inline static Comparison compare (unsigned i1, unsigned i2)
  { return i1 < i2 ? LESS : i1 == i2 ? EQUAL : GREATER; }
  /** Compare two size_t integers */
  inline static Comparison compare (size_t i1, size_t i2)
  { return i1 < i2 ? LESS : i1 == i2 ? EQUAL : GREATER; }
  /** Compare two floats */
  inline static Comparison compare (float f1, float f2)
  { return f1 < f2 ? LESS : f1 == f2 ? EQUAL : GREATER; }
  static bool stringToLong(const char*,long& result);
  static bool stringToUnsignedLong(const char*,unsigned long& result);
  static bool stringToLong(const string& str,long& result);
  static bool stringToInt(const string& str,int& result);
  static bool stringToInt(const char* str,int& result);
  static bool stringToUnsignedInt(const char* str,int& result);
  static bool stringToDouble(const char*,double& result);
  static bool stringToFloat(const char*,float& result);
  static bool stringToUnsigned64(const string& str,long long unsigned& result);
  static bool stringToUnsigned64(const char* str,long long unsigned& result);
  static int sign(int i);
  static int sign(long i);
  static int sign(double);
  static int max(int i,int j);
  static int min(int i,int j);
  static int gcd(int i,int j);
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


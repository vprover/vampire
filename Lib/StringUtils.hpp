/**
 * @file StringUtils.hpp
 * Defines class StringUtils.
 */

#ifndef __StringUtils__
#define __StringUtils__

#include "VString.hpp"
#include "DHMap.hpp"

namespace Lib {

using namespace std;

class StringUtils {
public:
  static vstring replaceChar(vstring str, char src, char target);
  static vstring sanitizeSuffix(vstring str);
  static bool isPositiveInteger(vstring str);
  static bool isPositiveDecimal(vstring str);
  static bool isBiggerThanZero(vstring str);

  static void splitStr(const char* str, char delimiter, Stack<vstring>& strings);
  static bool readEquality(const char* str, char eqChar, vstring& lhs, vstring& rhs);
  static bool readEqualities(const char* str, char delimiter, char eqChar, DHMap<vstring,vstring>& pairs);
};

}

#endif // __StringUtils__

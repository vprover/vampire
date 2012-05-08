/**
 * @file StringUtils.hpp
 * Defines class StringUtils.
 */

#ifndef __StringUtils__
#define __StringUtils__

#include <string>

#include "DHMap.hpp"

namespace Lib {

using namespace std;

class StringUtils {
public:
  static string replaceChar(string str, char src, char target);
  static string sanitizeSuffix(string str);
  static bool isPositiveInteger(string str);
  static bool isPositiveDecimal(string str);

  static void splitStr(const char* str, char delimiter, Stack<string>& strings);
  static bool readEquality(const char* str, char eqChar, string& lhs, string& rhs);
  static bool readEqualities(const char* str, char delimiter, char eqChar, DHMap<string,string>& pairs);
};

}

#endif // __StringUtils__

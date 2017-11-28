
/*
 * File StringUtils.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
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

  static void splitStr(const char* str, char delimiter, Stack<vstring>& strings);
  static bool readEquality(const char* str, char eqChar, vstring& lhs, vstring& rhs);
  static bool readEqualities(const char* str, char delimiter, char eqChar, DHMap<vstring,vstring>& pairs);
};

}

#endif // __StringUtils__

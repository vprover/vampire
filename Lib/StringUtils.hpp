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
 * @file StringUtils.hpp
 * Defines class StringUtils.
 */

#ifndef __StringUtils__
#define __StringUtils__

#include "VString.hpp"
#include "DHMap.hpp"
#include <cstdlib>

namespace Lib {

using namespace std;

template<class A> struct StringParser;

class StringUtils {
public:
  static vstring replaceChar(vstring str, char src, char target);
  static vstring sanitizeSuffix(vstring str);
  static bool isPositiveInteger(vstring str);
  static bool isPositiveDecimal(vstring str);

  static void splitStr(const char* str, char delimiter, Stack<vstring>& strings);
  static bool readEquality(const char* str, char eqChar, vstring& lhs, vstring& rhs);
  static bool readEqualities(const char* str, char delimiter, char eqChar, DHMap<vstring,vstring>& pairs);
  template<class A>
  static A parse(vstring const& str) 
  { return StringParser<A>{}(str); }
};

template<> struct StringParser<int> 
{
  int operator()(vstring const& str)
  { return atoi(str.c_str()); }
};


template<> struct StringParser<float> 
{
  float operator()(vstring const& str)
  { return atof(str.c_str()); }
};



}

#endif // __StringUtils__

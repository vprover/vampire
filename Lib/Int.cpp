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
 * @file Int.cpp
 *
 * @since 09/06/2000 Manchester
 */

#include <cstdio>
#include <cstdlib>
#include <cerrno>
#include <iostream>
#include <climits>

#include "Int.hpp"

using namespace Lib;

/**
 * Return the string representation of an integer.
 *
 * @param i integer
 * @since 27/05/2003 Manchester
 * @since 27/08/2003 Vienna, changed to return a string
 * @since 06/12/2003 Manchester, changed to use sprintf
 * @since 07/08/2014 Manchester, changed to return a std::string
 */
std::string Int::toString (int i)
{
  constexpr auto BUFSIZE = 20;
  char tmp [BUFSIZE];
  snprintf(tmp,BUFSIZE,"%d",i);
  std::string result(tmp);

  return result;
} // Int::toString (int i)


/**
 * Return the string representation of a double.
 *
 * @param d the double
 * @since 09/12/2003 Manchester
 */
std::string Int::toString(double d)
{
  constexpr auto BUFSIZE = 256;
  char tmp [BUFSIZE];
  snprintf(tmp,BUFSIZE,"%g",d);
  std::string result(tmp);

  return result;
} // Int::toString


/**
 * Return the string representation of a long.
 *
 * @param l the long
 * @since 10/02/2004 Manchester
 */
std::string Int::toString(long l)
{
  constexpr auto BUFSIZE = 256;
  char tmp [BUFSIZE];
  snprintf(tmp,BUFSIZE,"%ld",l);
  std::string result(tmp);

  return result;
} // Int::toString


/**
 * Return the string representation of an unsigned integer.
 * @since 10/02/2004 Manchester
 */
std::string Int::toString(unsigned i)
{
  constexpr auto BUFSIZE = 256;
  char tmp [BUFSIZE];
  snprintf(tmp,BUFSIZE,"%u",i);
  std::string result(tmp);

  return result;
} // Int::toString

/**
 * Return the string representation of an unsigned integer.
 */
std::string Int::toString(unsigned long i)
{
  constexpr auto BUFSIZE = 256;
  char tmp [BUFSIZE];
  snprintf(tmp,BUFSIZE,"%lu",i);
  std::string result(tmp);

  return result;
} // Int::toString

std::string Int::toHexString(size_t i)
{
  constexpr auto BUFSIZE = 256;
  char tmp [BUFSIZE];
  snprintf(tmp,BUFSIZE,"0x%zx",i);
  std::string result(tmp);

  return result;
} // Int::toString


/**
 * Convert a string to a long value.
 * @since 30/08/2004 Torrevieja
 * @since 15/11/2004 Manchester, changed to check for overflow
 * @since 27/09/2005 Redmond, check on empty string added
 */
bool Int::stringToLong (const char* str,long& result)
{
  if (! *str) { // empty string
    return false;
  }

  errno = 0;
  char* endptr = 0;
  result = strtol(str,&endptr,10);

  if (*endptr ||
      (result == 0 && errno) ||
      ( (result == LONG_MAX || result == LONG_MIN) && errno==ERANGE ) ) { // error returned by strtol
    return false;
  }

  return true;
} // Int::stringToLong


/**
 * Convert a std::string to an integer value.
 * @since 30/08/2004 Torrevieja
 */
bool Int::stringToInt (const std::string& str,int& result)
{
  return stringToInt(str.c_str(),result);
} // Int::stringToInt

/**
 * Convert a std::string to an unsigned integer value.
 * @since 20/09/2009 Redmond
 */
bool Int::stringToUnsignedInt (const std::string& str,unsigned& result)
{
  return stringToUnsignedInt(str.c_str(),result);
} // Int::stringToUnsignedInt

/**
 * Convert a string to an unsigned integer value.
 * @since 15/11/2004 Manchester
 * @since 25/08/2022 Prague
 */
bool Int::stringToUnsignedInt (const char* str,unsigned& result)
{
  if (! *str) { // empty string
    return false;
  }

  errno = 0;           // to fail on "rubbish instead of number"
  char* endptr = 0;    // to fail on "rubbish after number"
  result = strtoul(str,&endptr,10);

  // careful strtoul will still happily take numbers larger or even smaller (i.e. negative) than the representable range and produce some value

  return (errno == 0 && !*endptr);
} // Int::stringToUnsignedInt

/**
 * Convert a string to an integer value.
 *
 * @since 30/08/2004 Torrevieja
 * @since 15/11/2004 Manchester, changed to check for overflow
 */
bool Int::stringToInt (const char* str,int& result)
{
  long ln;
  bool converted = stringToLong(str,ln);
  if (! converted || ln > INT_MAX || ln < INT_MIN) {
    return false;
  }
  result = (int)ln;
  return true;
} // Int::stringToInt


/**
 * Convert a string to a double value.
 *
 * @since 15/11/2004 Manchester
 */
bool Int::stringToDouble (const char* str,double& result)
{
  errno = 0;
  char* endptr = 0;
  result = strtod(str,&endptr);

  if (*endptr ||
      (result == 0.0 && errno)) { // error returned by strtol
    return false;
  }

  return true;
} // Int::stringToDouble


/**
 * Convert a string to a float value.
 *
 * @since 15/11/2004 Manchester
 */
bool Int::stringToFloat (const char* str,float& result)
{
  double d;
  bool converted = stringToDouble(str,d);
//   if (! converted || d > FLOAT_MAX || d < FLOAT_MIN) {
//     return false;
//   }
  if (! converted) {
    return false;
  }
  result = (float)d;
  return true;
} // Int::stringToInt


/**
 * Convert a string to a 64-bit unsigned. No overflow check is made.
 *
 * @since 30/11/2006 Haifa
 */
bool Int::stringToUnsigned64 (const char* str,long long unsigned& result)
{
  result = 0;
  if (! *str) { // empty string
    return false;
  }
  // sip leading 0s
  while (*str == '0') {
    str++;
  }
  while (*str) {
    char nextChar = *str;
    str++;
    if (nextChar < '0' || nextChar > '9') {
      return false;
    }
    result = 10*result + (nextChar - '0');
  }
  return true;
} // Int::stringToUnsigned64

/**
 * Convert a std::string to a 64-bit unsigned. No overflow check is made.
 *
 * @since 30/11/2006 Haifa
 */
bool Int::stringToUnsigned64 (const std::string& str,long long unsigned& result)
{
  return stringToUnsigned64(str.c_str(),result);
} // Int::stringToUnsigned64

/**
 * True if @b str is a string representing an (arbitrary precision) integer.
 * @since 30/07/2010 Linz
 */
bool Int::isInteger(const char* str)
{
	if (*str == '-') {
		str++;
	}

	// str must represent a non-negative integer
	if (! *str) {
		return false;
	}

	// str is non-empty and must represent a non-negative integer
	do {
		if (*str < '0' || *str > '9') {
			return false;
		}
		str++;
	}
	while (*str);

	return true;
} // Int::isInteger


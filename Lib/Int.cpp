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
#include "../Debug/Tracer.hpp"

namespace Lib {

/**
 * Return the string representation of an integer.
 *
 * @param i integer
 * @since 27/05/2003 Manchester
 * @since 27/08/2003 Vienna, changed to return a string
 * @since 06/12/2003 Manchester, changed to use sprintf
 */
string Int::toString (int i)
{
  char tmp [20];
  sprintf(tmp,"%d",i);
  string result(tmp);

  return result;
} // Int::toString (int i)


/**
 * Return the string representation of a double.
 *
 * @param d the double
 * @since 09/12/2003 Manchester
 */
string Int::toString(double d)
{
  char tmp [256];
  sprintf(tmp,"%g",d);
  string result(tmp);

  return result;
} // Int::toString


/**
 * Return the string representation of a long.
 *
 * @param l the long
 * @since 10/02/2004 Manchester
 */
string Int::toString(long l)
{
  char tmp [256];
  sprintf(tmp,"%ld",l);
  string result(tmp);

  return result;
} // Int::toString


/**
 * Return the string representation of an unsigned integer.
 * @since 10/02/2004 Manchester
 */
string Int::toString(unsigned i)
{
  char tmp [256];
  sprintf(tmp,"%d",i);
  string result(tmp);

  return result;
} // Int::toString

/**
 * Return the string representation of an unsigned integer.
 * @since 10/02/2004 Manchester
 */
string Int::toString(size_t i)
{
  char tmp [256];
  sprintf(tmp,"%zd",i);
  string result(tmp);

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
  CALL("Int::stringToLong");

  if (! *str) { // empty string
    return 0;
  }

  errno = 0;
  char* endptr = 0;
  result = strtol(str,&endptr,10);

  if (*endptr || 
      (result == 0 && errno)) { // error returned by strtol

    return false;
  }

  return true;
} // Int::stringToLong


/**
 * Convert a string to an integer value. 
 * @since 30/08/2004 Torrevieja
 */
bool Int::stringToInt (const string& str,int& result)
{
  CALL("Int::stringToInt");

  return stringToInt(str.c_str(),result);
} // Int::stringToInt


/**
 * Convert a string to an unsigned integer value. 
 * @since 15/11/2004 Manchester
 */
bool Int::stringToUnsignedInt (const char* str,int& result)
{
  CALL("Int::stringToUnsignedInt");

  return stringToInt(str,result) && 
         result >= 0;
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
  CALL("Int::stringToDouble");

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
 * Convert a string to a 64-bit unsigned. No overflow check is made.
 * 
 * @since 30/11/2006 Haifa
 */
bool Int::stringToUnsigned64 (const string& str,long long unsigned& result)
{
  return stringToUnsigned64(str.c_str(),result);
} // Int::stringToUnsigned64


}

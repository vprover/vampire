/**
 * @file StringUtils.cpp
 * Implements class StringUtils.
 */

#include "DArray.hpp"

#include "StringUtils.hpp"

namespace Lib
{

using namespace std;

string StringUtils::replaceChar(string str, char src, char target)
{
  CALL("StringUtils::replaceChar");

  size_t len=str.size();
  static DArray<char> buf;
  buf.ensure(len);

  const char* sptr=str.c_str();
  char* tptr=buf.array();

  while(*sptr) {
    if(*sptr==src) {
      *tptr=target;
    }
    else {
      *tptr=*sptr;
    }
    tptr++;
    sptr++;
  }
  return string(buf.array(), len);
}

/**
 * Sanitize string so that it can be used as a valid suffix in the
 * Signature::addFreshFunction() and Signature::addFreshPredicate()
 * functions.
 */
string StringUtils::sanitizeSuffix(string str)
{
  CALL("StringUtils::sanitizeSuffix");

  size_t len=str.size();
  static DArray<char> buf;
  buf.ensure(len);

  const char* sptr=str.c_str();
  char* tptr=buf.array();

  while(*sptr) {
    char c = *sptr;

    switch(c) {
    case '(':
    case ')':
    case '"':
    case '\'':
    case '$':
    case '%':
    case ',':
    case '.':
      c = '_';
      break;
    default: break;
    }

    *tptr = c;
    tptr++;
    sptr++;
  }
  return string(buf.array(), len);
}

}

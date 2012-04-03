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

bool StringUtils::isPositiveInteger(string str)
{
  CALL("StringUtils::isPositiveInteger");

  size_t sz = str.size();

  if(str[0]=='0') {
    return sz==1;
  }
  for(size_t i=0; i<sz; i++) {
    if(str[i]<'0' || str[i]>'9') {
      return false;
    }
  }
  return true;
}

bool StringUtils::isPositiveDecimal(string str)
{
  CALL("StringUtils::isPositiveDecimal");

  size_t sz = str.size();

  size_t i = 0;
  if(str[0]=='0') {
    if(sz==1) { return true; }
    if(str[1]!='.') { return false; }
    i = 1;
  }
  bool seenPoint = false;
  for(; i<sz; i++) {
    if(str[i]=='.') {
      if(i==0 || seenPoint) { return false; }
      seenPoint = true;
    }
    else if(str[i]<'0' || str[i]>'9') {
      return false;
    }
  }
  return true;
}

}

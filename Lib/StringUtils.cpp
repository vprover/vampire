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
 * @file StringUtils.cpp
 * Implements class StringUtils.
 */

#include "DArray.hpp"
#include "DHMap.hpp"
#include "Stack.hpp"

#include "StringUtils.hpp"

namespace Lib
{

using namespace std;

vstring StringUtils::replaceChar(vstring str, char src, char target)
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
  return vstring(buf.array(), len);
}

/**
 * Sanitize vstring so that it can be used as a valid suffix in the
 * Signature::addFreshFunction() and Signature::addFreshPredicate()
 * functions.
 */
vstring StringUtils::sanitizeSuffix(vstring str)
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
  return vstring(buf.array(), len);
}

bool StringUtils::isPositiveInteger(vstring str)
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

bool StringUtils::isPositiveDecimal(vstring str)
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

void StringUtils::splitStr(const char* str, char delimiter, Stack<vstring>& strings)
{
  CALL("StringUtils::splitStr");

  static Stack<char> currPart;
  currPart.reset();

  const char* curr = str;
  while(*curr) {
    if(*curr==delimiter) {
      currPart.push(0);
      strings.push(currPart.begin());
      currPart.reset();
    }
    else {
      currPart.push(*curr);
    }
    curr++;
  }
  currPart.push(0);
  strings.push(currPart.begin());
}

bool StringUtils::readEquality(const char* str, char eqChar, vstring& lhs, vstring& rhs)
{
  CALL("StringUtils::readEquality");

  static Stack<vstring> parts;
  parts.reset();
  splitStr(str, eqChar, parts);
  if(parts.size()!=2) {
    return false;
  }
  lhs = parts[0];
  rhs = parts[1];
  return true;
}

/**
 * If str doesn't contain equalities, false is returned and the content of pairs is undefined.
 */
bool StringUtils::readEqualities(const char* str, char delimiter, char eqChar, DHMap<vstring,vstring>& pairs)
{
  CALL("StringUtils::readEqualities");

  static Stack<vstring> parts;
  parts.reset();
  splitStr(str, delimiter, parts);

  Stack<vstring>::TopFirstIterator pit(parts);
  while(pit.hasNext()) {
    vstring part = pit.next();
    vstring lhs, rhs;
    if(!readEquality(part.c_str(), eqChar, lhs, rhs)) {
      return false;
    }
    pairs.set(lhs, rhs);
  }
  return true;
}

}

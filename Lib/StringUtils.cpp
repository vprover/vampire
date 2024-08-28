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

void StringUtils::dropEmpty(Stack<vstring>& strings)
{
  unsigned i = 0;
  for (unsigned j = 0; j < strings.size(); j++) {
    if (strings[j].size() > 0) {
      strings[i++] = strings[j];
    }
  }
  strings.truncate(i);
}

bool StringUtils::readEquality(const char* str, char eqChar, vstring& lhs, vstring& rhs)
{
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


/**
 * Let us define a similarity measure for strings, used to compare option names 
 * 
 * This is a Levenshtein (edit) distance and therefore gives the number
 * of edits needed to change s1 into s2
 *
 * @author Giles
 */
size_t StringUtils::distance(const vstring &s1, const vstring &s2)
{
  const size_t m(s1.size());
  const size_t n(s2.size());

  if( m==0 ) return n;
  if( n==0 ) return m;

  DArray<size_t> costs = DArray<size_t>(n+1);

  for( size_t k=0; k<=n; k++ ) costs[k] = k;

  size_t i = 0;
  for ( vstring::const_iterator it1 = s1.begin(); it1 != s1.end(); ++it1, ++i )
  {
    costs[0] = i+1;
    size_t corner = i;

    size_t j = 0;
    for ( vstring::const_iterator it2 = s2.begin(); it2 != s2.end(); ++it2, ++j )
    {
      size_t upper = costs[j+1];
      if( *it1 == *it2 ){costs[j+1] = corner;}
      else{
        size_t t(upper<corner?upper:corner);
        costs[j+1] = (costs[j]<t?costs[j]:t)+1;
      }
      corner = upper;
    }
  }

  return costs[n];
}

}

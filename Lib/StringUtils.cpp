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

std::string StringUtils::replaceChar(std::string str, char src, char target)
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
  return std::string(buf.array(), len);
}

void StringUtils::replaceAll(std::string& where, const std::string& from, const std::string& to)
{
  if(from.empty())
    return;
  size_t start_pos = 0;
  while((start_pos = where.find(from, start_pos)) != std::string::npos) {
    where.replace(start_pos, from.length(), to);
    start_pos += to.length(); // don't recurse into "to" in case "from" would be its substring
  }
}

/**
 * Sanitize std::string so that it can be used as a valid suffix in the
 * Signature::addFreshFunction() and Signature::addFreshPredicate()
 * functions.
 */
std::string StringUtils::sanitizeSuffix(std::string str)
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
  return std::string(buf.array(), len);
}

bool StringUtils::isPositiveInteger(std::string str)
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

bool StringUtils::isPositiveDecimal(std::string str)
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

void StringUtils::splitStr(const char* str, char delimiter, Stack<std::string>& strings)
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

void StringUtils::dropEmpty(Stack<std::string>& strings)
{
  unsigned i = 0;
  for (unsigned j = 0; j < strings.size(); j++) {
    if (strings[j].size() > 0) {
      strings[i++] = strings[j];
    }
  }
  strings.truncate(i);
}

bool StringUtils::readEquality(const char* str, char eqChar, std::string& lhs, std::string& rhs)
{
  static Stack<std::string> parts;
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
bool StringUtils::readEqualities(const char* str, char delimiter, char eqChar, DHMap<std::string,std::string>& pairs)
{
  static Stack<std::string> parts;
  parts.reset();
  splitStr(str, delimiter, parts);

  Stack<std::string>::TopFirstIterator pit(parts);
  while(pit.hasNext()) {
    std::string part = pit.next();
    std::string lhs, rhs;
    if(!readEquality(part.c_str(), eqChar, lhs, rhs)) {
      return false;
    }
    pairs.set(lhs, rhs);
  }
  return true;
}

}

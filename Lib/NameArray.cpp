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
 * @file NameArray.cpp
 * Implements ordered immutable arrays of integers.
 * Previously they were used in Options.
 *
 * @since 21/04/2005 Manchester
 */

#include <cstring>

#include "Exception.hpp"
#include "NameArray.hpp"
#include "Debug/Tracer.hpp"

namespace Lib {

NameArray::NameArray (const char* array[],int len)
  : length(len),
    _array(array)
{
#if VDEBUG
  for (int i=1; i<len; i++) {
    ASS_REP2(strcmp(array[i-1],array[i]) < 0,
	     array[i-1],
	     array[i]);
  }
#endif
} // NameArray::NameArray

/**
 * Find the index of a string in the name array. Throw a
 * ValueNotFoundException if it is not present.
 *
 * @return the index
 * @since 12/11/2004 Manchester
 */
int NameArray::find (const char* value) const
{
  CALL("NameArray::find");

  int res=tryToFind(value);
  if(res==-1) {
    throw ValueNotFoundException();
  }
  return res;
} // Options::find

/**
 * Find the index of a string in the name array. Return -1
 * if it is not present.
 */
int NameArray::tryToFind(const char* value) const
{
  CALL("NameArray::tryToFind");

  int from = 0;
  int to = length;
  while (from < to) {
    int mid = (from+to)/2;
    int comp = strcmp(_array[mid],value);
    if (comp < 0) {
      from = mid+1;
    }
    else if (comp == 0) {
      return mid;
    }
    else { // comp > 0
      to = mid;
    }
  }
  return -1;
}

} // namespace Lib

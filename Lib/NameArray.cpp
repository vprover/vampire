/**
 * @file NameArray.cpp
 * Implements ordered immutable arrays of integers.
 * Previously they were used in Options.
 *
 * @since 21/04/2005 Manchester
 */

#include <cstring>

#include "NameArray.hpp"
#include "../Debug/Tracer.hpp"

namespace Lib {

NameArray::NameArray (const char* array[],int len)
  : length(len),
    _array(array)
    
{
} // NameArray::NameArray

/**
 * Find the index of a string in the name array.
 *
 * @return the index, if found, and -1 if not
 * @since 12/11/2004 Manchester
 */
int NameArray::find (const char* value) const
{
  CALL("NameArray::find");

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
} // Options::find


} // namespace Lib

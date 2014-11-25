/**
 * @file NameArray.hpp
 * Defines ordered immutable arrays of integers.
 * Previously they were used in Options.
 *
 * TODO : not currently used, but could be used in OptionValues
 *
 * @since 21/04/2005 Manchester
 */

#ifndef __NameArray__
#define __NameArray__

using namespace std;

namespace Lib {

/**
 * Defines ordered immutable arrays of integers.
 * Previously they were used in Options.
 *
 * @since 21/04/2005 Manchester
 */
class NameArray {
public:
  NameArray(const char* array[],int length);
  int find(const char* value) const;
  int tryToFind(const char* value) const;
  /** Return i-th element of the array */
  const char* operator[] (int i) const { return _array[i]; }
  /** The length of the array */
  const int length;
private:
  /** Array itself */
  const char** _array;
}; // class NameArray

}

#endif

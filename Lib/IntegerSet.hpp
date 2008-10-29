/**
 * @file IntegerSet.hpp
 * Defines class IntegerSet for sets of nonnegative integers.
 *
 * @since 16/06/2005 Manchester
 */

#ifndef __IntegerSet__
#define __IntegerSet__

#define BITS_PER_INT (8*sizeof(unsigned int))

namespace Lib {

/**
 * Class IntegerSet for sets of nonnegative integers.
 *
 * @since 16/06/2005 Manchester
 */
class IntegerSet
{
public:
  IntegerSet() : _words(0), _set(0) {}
  ~IntegerSet();
  void insert(int n);
  void remove(int n);
  bool member(int n) const;
private:
  /** the number of words used by this set */
  int _words;
  /** the set itself coded as an array of unsigned integers */
  unsigned int* _set;
}; // class IntegerSet

} // namespace Lib

#endif

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
 * @file MultiCounter.hpp
 * Defines a class MultiCounter that is, essentially, an array of counters
 * indexed by unsigned integers.
 *
 * @since 06/01/2004, Manchester
 * @since 22/08/2023, just ZIArray
 */

#ifndef __MultiCounter__
#define __MultiCounter__

#include "Lib/Array.hpp"

namespace Lib {

/**
 * Implements a class that counts the number of occurrences of
 * variables.
 */
class MultiCounter
{
public:
  /**
   * Increment the counter number v by one.
   * @since 06/01/2004 Manchester
   */
  void inc(int v) { _counts[v]++; }

  /**
   * Decrement the counter number v by one.
   * @since 16/01/2004 Manchester
   */
  void dec(int v) { _counts[v]--; }

  /** 
   * Get the value of the counter v.
   * @since 16/01/2004 Manchester changed to new representation of variables
   */
  int get(int v) { return _counts[v]; }

private:
  ZIArray<int> _counts;
}; // class MultiCounter

}

#endif // __MultiCounter__

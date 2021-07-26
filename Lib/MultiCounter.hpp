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
 */

#ifndef __MultiCounter__
#define __MultiCounter__

#include "Debug/Assertion.hpp"

namespace Lib {

/**
 * Implements a class that counts the number of occurrences of
 * variables.
 */
class MultiCounter
{
public:
  /** create an empty collection */
  MultiCounter()
    :  _top(0),
       _counts(0)
  {}

  ~MultiCounter();

/**
 * Increment the counter number v by one.
 * @since 06/01/2004 Manchester
 */
  void inc(int v)
  {
    if (v >= _top) { // not enough capacity
      expandToFit(v);
    }
    ASS(_counts);
    _counts[v]++;
  } // MultiCount::inc

  /**
   * Decrement the counter number v by one.
   * @since 16/01/2004 Manchester
   */
  void dec(int v)
  {
    if (v >= _top) { // not enough capacity
      expandToFit(v);
    }
    ASS(_counts);
    _counts[v]--;
  } // MultiCount::dec

  /**
   * Set the counter number v to the value c.
   * @since 16/01/2004 Manchester
   */
  void set(int v, int c)
  {
    if (v >= _top) { // not enough capacity
      expandToFit(v);
    }
    ASS(_counts);
    _counts[v] = c;
  } // MultiCounter::set

  /** 
   * Get the value of the counter v.
   * @since 16/01/2004 Manchester changed to new representation of variables
   */
  int get(int v) const
  {
    return v < _top ? _counts[v] : 0; 
  } // MultiCounter::get

  /** 
   * Get the value of the counter v assuming that this counter
   * was initialised.
   * @since 31/03/2006 Redmond
   */
  int unsafeGet(int v) const
  {
    ASS(v < _top);
    return _counts[v]; 
  } // MultiCounter::unsafeGet

  /** Return the last possible counter */
  int lastCounter() const
  { return _top-1; }

private:
  /** _top-1 is the last positive variable that can be accessed */
  int _top;
  /** points to variable 0 */
  int* _counts;
  void expandToFit(int v);
}; // class MultiCounter

}

#endif // __MultiCounter__

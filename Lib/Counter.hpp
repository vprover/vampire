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
 * @file Counter.hpp
 * Defines counters.
 * @since 14/03/2006 Bellevue
 */

#ifndef __Counter__
#define __Counter__

namespace Lib {

/**
 * Class Counter.
 * Implements counters, count from 0.
 * @since 14/03/2006 Bellevue
 */
class Counter
{
public:
  /** Initialise the counter to 0 */
  Counter : _value(0) {}
  /** Increase the counter by n */
  void inc(int n) { _value += n; }
  /** Increase the counter by 1 */
  void inc() { _value++; } 
  /** Decrease the counter by n */
  void dec(int n) { _value -= n; }
  /** Decrease the counter by 1 */
  void dec() { _value--; }
  /** Reset the counter to n */
  void reset(int n) { _value = n; }
  /** Return the value of the counter */
  int value() const { return _value; }
private:
  /** The value of the counter */
  int _value;
}; // class Counter

}

#endif



/*
 * File Enumerator.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file Enumerator.hpp
 * Defines enumerators that are used to enumerate whatever (e.g., clauses).
 * @since 18/12/2005 Bellevue
 */

#ifndef __Enumerator__
#define __Enumerator__

namespace Lib {

/**
 * Class Enumerator
 * Implements enumerators that are used to enumerate whatever
 * (e.g., clauses).
 * @since 18/12/2005 Bellevue
 */
class Enumerator
{
public:
  Enumerator() : _lastNumber(0) {}
  /** Return the new number */
  unsigned newNumber() { return ++_lastNumber;}
  /** Return the last number */
  unsigned lastNumber() { return _lastNumber;}
private:
  /** last number */
  unsigned _lastNumber;
public:
  /** Unit enumerator */
  static Enumerator unitEnumerator;
}; // class Enumerator


}

#endif



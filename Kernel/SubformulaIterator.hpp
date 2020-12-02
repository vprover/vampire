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
 * @file SubformulaIterator.hpp
 * Defines a class SubformulaIterator that iterates
 * over subformulas in formula lists and formulas.
 *
 * @since 06/01/2004, Manchester
 */

#ifndef __SubformulaIterator__
#define __SubformulaIterator__

#include "Lib/VirtualIterator.hpp"

#include "Formula.hpp"

namespace Kernel {

/**
 * Implements an iterator over subformulas of a formula or formula list.
 */
class SubformulaIterator
: public IteratorCore<Formula*>
{
public:
  SubformulaIterator (Formula*);
  SubformulaIterator (FormulaList*);
  ~SubformulaIterator ();

  bool hasNext ();
  Formula* next ();
  Formula* next (int& polarity);
private:
  class Element;
  Formula* _current;
  int _currentPolarity;
  Element* _reserve;
}; // class SubformulaIterator

}

#endif // __SubformulaIterator__



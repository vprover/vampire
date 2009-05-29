/**
 * @file SubformulaIterator.hpp
 * Defines a class SubformulaIterator that iterates
 * over subformulas in formula lists and formulas.
 *
 * @since 06/01/2004, Manchester
 */

#ifndef __SubformulaIterator__
#define __SubformulaIterator__

#include "Formula.hpp"

namespace Kernel {

/**
 * Implements an iterator over variables of a formula formula list, or atom.
 */
class SubformulaIterator
{
public:
  SubformulaIterator (Formula*);
  SubformulaIterator (FormulaList*);
  ~SubformulaIterator ();

  bool hasNext ();
  Formula* next ();
private:
  class Element;
  Formula* _current;
  Element* _reserve;
}; // class SubformulaIterator

}

#endif // __SubformulaIterator__



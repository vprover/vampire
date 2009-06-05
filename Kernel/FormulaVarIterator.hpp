/**
 * @file FormulaVarIterator.hpp
 * Defines a class FormulaVarIterator that iterates
 * over free variables in a formula.
 *
 * @since 06/01/2004, Manchester
 */

#ifndef __FormulaVarIterator__
#define __FormulaVarIterator__

#include "../Lib/MultiCounter.hpp"

#include "Formula.hpp"

using namespace Lib;

namespace Kernel {

class TermList;

/**
 * Implements an iterator over free variables of a
 * formula formula list, or atom.
 *
 * @warning works correctly only for formulas in which free variables
 *          are different from bound
 *
 * @since 06/01/2004, Manchester
 */
class FormulaVarIterator
{
public:
  FormulaVarIterator(const Formula*);
  FormulaVarIterator(const FormulaList*);
  ~FormulaVarIterator();

  bool hasNext();
  int next();
private:
  class Element;
  /** current term, may be 0 */
  const TermList* _current;
  /** reserve element */
  Element* _reserve;
  /** Counter used to store bound variables */
  MultiCounter _bound;
  void popReserve ();
}; // class FormulaVarIterator

}

#endif // __FormulaVarIterator__

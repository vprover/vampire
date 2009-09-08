/**
 * @file FormulaVarIterator.hpp
 * Defines a class FormulaVarIterator that iterates
 * over free variables in a formula.
 *
 * @since 06/01/2004, Manchester
 * @since 02/09/2009 Redmond, reimplemented to work with non-rectified
 * formulas and return each variable only once
 */

#ifndef __FormulaVarIterator__
#define __FormulaVarIterator__

#include "../Lib/MultiCounter.hpp"
#include "../Lib/Stack.hpp"

#include "../Kernel/Term.hpp"
#include "../Kernel/Formula.hpp"

using namespace Lib;

namespace Kernel {

/**
 * Implements an iterator over free variables of a
 * formula formula list, or atom.
 *
 * @since 06/01/2004, Manchester
 * @since 02/09/2009 Redmond, reimplemented to work with non-rectified
 * formulas and return each variable only once
 */
class FormulaVarIterator
{
public:
  explicit FormulaVarIterator(const Formula*);
  bool hasNext();
  int next();

private:
  /** instruction of what to process next */
  enum Instruction {
    /** process formula */
    FVI_FORMULA,
    /** process term */
    FVI_TERM,
    /** unbind variables bound by the quantifier in a quantified formula */
    FVI_UNBIND
  }; //

  /** If true then _nextVar contains the next variable   */
  bool _found;
  /** The variable to be returned by next() */
  unsigned _nextVar;

  /** Counter used to store bound variables, together with the number of times they are bound */
  MultiCounter _bound;
  /** To store previosly found free variables */
  MultiCounter _free;
  /** List of formulas to be processed */
  Stack<const Formula*> _formulas;
  /** List of term lists to process */
  Stack<const TermList*> _terms;
  /** list of instructions telling what to do next */
  Stack<Instruction> _instructions;
}; // class FormulaVarIterator

}

#endif // __FormulaVarIterator__

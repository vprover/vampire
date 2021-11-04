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
 * @file FormulaVarIterator.hpp
 * Defines a class FormulaVarIterator that iterates
 * over free variables in a formula or a term.
 *
 * @since 06/01/2004, Manchester
 * @since 02/09/2009 Redmond, reimplemented to work with non-rectified
 * formulas and return each variable only once
 * @since 15/05/2015 Gothenburg, FOOL support added
 */

#ifndef __FormulaVarIterator__
#define __FormulaVarIterator__

#include "Lib/MultiCounter.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/Term.hpp"
#include "Kernel/Formula.hpp"

using namespace Lib;

namespace Kernel {

/**
 * Implements an iterator over free variables of a
 * formula, a term or a list of terms.
 *
 * Any argument may contain $let and $ite expressions.
 *
 * @since 06/01/2004, Manchester
 * @since 02/09/2009 Redmond, reimplemented to work with non-rectified
 * formulas and return each variable only once
 * @since 15/05/2015 Gothenburg, FOOL support added
 */
class FormulaVarIterator
{
public:
  DECL_ELEMENT_TYPE(unsigned);
  explicit FormulaVarIterator(const Formula*);
  explicit FormulaVarIterator(const Term*);
  explicit FormulaVarIterator(const TermList*);

  bool hasNext();
  unsigned next();

private:
  /** instruction of what to process next */
  enum Instruction {
    /** process formula */
    FVI_FORMULA,
    /** process term */
    FVI_TERM,
    /** process term list */
    FVI_TERM_LIST,
    /** bind variables bound by quantifier or $let */
    FVI_BIND,
    /** unbind variables bound by quantifier or $let */
    FVI_UNBIND,
  };

  /** If true then _nextVar contains the next variable   */
  bool _found;
  /** The variable to be returned by next() */
  unsigned _nextVar;

  /** Counter used to store bound variables, together with the number of times they are bound */
  MultiCounter _bound;
  /** To store previously found free variables */
  MultiCounter _free;
  /** Stack of formulas to be processed */
  Stack<const Formula*> _formulas;
  /** Stack of terms to process */
  Stack<const Term*> _terms;
  /** Stack of term lists to process */
  Stack<TermList> _termLists;
  /** Stack of instructions telling what to do next */
  Stack<Instruction> _instructions;
  /** Stack of lists of variables to process */
  Stack<const VList*> _vars;
}; // class FormulaVarIterator

}

#endif // __FormulaVarIterator__

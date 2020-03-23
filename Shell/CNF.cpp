
/*
 * File CNF.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file CNF.cpp
 * Implements class CNF implementing CNF transformation.
 * @since 19/01/2004 Manchester
 * @since 27/12/2007 Manchester, changed completely to a new implementation
 */

#include "Debug/Tracer.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "CNF.hpp"

using namespace Kernel;
using namespace Shell;

/**
 * Initialise the CNF object.
 * @since 27/12/2007 Manchester
 */
CNF::CNF()
  : _literals(16),
    _formulas(16)
{
} // CNF::CNF

/**
 * Convert @b unit to CNF and push the resulting clauses on @b stack
 * @pre @b unit must be a formula unit
 * @since 27/12/2007 Manchester
 */
void CNF::clausify (Unit* unit,Stack<Clause*>& stack)
{
  CALL("CNF::clausify/2");
  ASS(! unit->isClause());

  _unit = static_cast<FormulaUnit*>(unit);
  _result = &stack;
  _literals.reset();
  _formulas.reset();

  Formula* f = _unit->formula();
  switch (f->connective()) {
  case TRUE:
    return;
  case FALSE:
    {
      // create an empty clause and push it in the stack
      Clause* clause = new(0) Clause(0,
				     unit->inputType(),
				     new Inference1(Inference::CLAUSIFY,unit));
      stack.push(clause);
    }
    return;
  default:
    clausify(f);
  }
} // CNF::clausify()


/**
 * Clausify the formula f \/ F1 \/ ... \/ Fn \/ L1 \/ ... \/ Lm,
 * where [F1,...,Fn] is the content of _formulas and [L1,...,Lm]
 * is the content of _literals. After the clausification restore
 * the stacks _formulas and _literals to their state before the call.
 *
 * @since 27/12/2007 Manchester
 */
void CNF::clausify (Formula* f)
{
  CALL("CNF::clausify/1");

  switch (f->connective()) {
  case LITERAL:
    _literals.push(f->literal());
    if (_formulas.isEmpty()) {
      // collect the clause
      int length = _literals.length();
      Clause* clause = new(length) Clause(length,
					  _unit->inputType(),
					  new Inference1(Inference::CLAUSIFY,
							 _unit));;
      for (int i = length-1;i >= 0;i--) {
	(*clause)[i] = _literals[i];
      }
      _result->push(clause);
    }
    else {
      f = _formulas.pop();
      clausify(f);
      _formulas.push(f);
    }
    _literals.pop();
    return;

  case AND:
    {
      FormulaList::Iterator fs(f->args());
      while (fs.hasNext()) {
	clausify(fs.next());
      }
    }
    return;

  case OR:
    {
      int ln = _formulas.length();

      FormulaList::Iterator fs(f->args());
      while (fs.hasNext()) {
	_formulas.push(fs.next());
      }
      clausify(_formulas.pop());
      _formulas.truncate(ln);
    }
    return;

  case FORALL:
    clausify(f->qarg());
    return;

  default:
    ASSERTION_VIOLATION;
  }
} // CNF::clausify


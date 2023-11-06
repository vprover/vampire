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
 * @file CNF.cpp
 * Implements class CNF implementing CNF transformation.
 * @since 19/01/2004 Manchester
 * @since 27/12/2007 Manchester, changed completely to a new implementation
 */


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
				     FormulaTransformation(InferenceRule::CLAUSIFY,unit));
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
/*
void CNF::clausify_rec (Formula* f)
{
  switch (f->connective()) {
  case LITERAL:
    _literals.push(f->literal());
    if (_formulas.isEmpty()) {
      // collect the clause
      int length = _literals.length();
      Clause* clause = new(length) Clause(length,
          FormulaTransformation(InferenceRule::CLAUSIFY,_unit));
      for (int i = length-1;i >= 0;i--) {
	      (*clause)[i] = _literals[i];
      }
      _result->push(clause);
    }
    else {
      f = _formulas.pop();
      clausify_rec(f);
      _formulas.push(f);
    }
    _literals.pop();
    return;

  case AND:
    {
      FormulaList::Iterator fs(f->args());
      while (fs.hasNext()) {
	      clausify_rec(fs.next());
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
      clausify_rec(_formulas.pop());
      _formulas.truncate(ln);
    }
    return;

  case FORALL:
    clausify_rec(f->qarg());
    return;

  default:
    ASSERTION_VIOLATION;
  }
}*/ // CNF::clausify

/**
 * A recursion-free implementation of the above.
 */
void CNF::clausify(Formula* f)
{
  enum TodoTag {
    MAIN,     // needs a Formula*
    LIT_REST, // needs a Formula*
    AND_REST, // needs a FormulaList*
    OR_REST,  // needs an int
  };
  union TodoVal {
    Formula* aFla;
    FormulaList* aFlist;
    int anInt;
  };

  Stack<std::pair<TodoTag,TodoVal>> todo;
  todo.push(std::make_pair<TodoTag,TodoVal>(MAIN,{.aFla = f}));

  do {
    ASS(todo.isNonEmpty());
    auto task = todo.pop();

    switch(task.first) {
      case MAIN: {
        Formula* f = task.second.aFla;

        formula_reset:

        switch (f->connective()) {
        case LITERAL:
          _literals.push(f->literal());
          if (_formulas.isEmpty()) {
            // collect the clause
            int length = _literals.length();
            Clause* clause = new(length) Clause(length,
                FormulaTransformation(InferenceRule::CLAUSIFY,_unit));
            for (int i = length-1;i >= 0;i--) {
              (*clause)[i] = _literals[i];
            }
            _result->push(clause);
            _literals.pop();
          }
          else {
            f = _formulas.pop();
            todo.push(std::make_pair<TodoTag,TodoVal>(LIT_REST,
              {.aFla = f}));
            todo.push(std::make_pair<TodoTag,TodoVal>(MAIN,
              {.aFla = f}));
          }
          break;

        case AND:
          {
            FormulaList* fl = f->args();
            if (FormulaList::isNonEmpty(fl)) {
              todo.push(std::make_pair<TodoTag,TodoVal>(AND_REST,
                {.aFlist = fl->tail()}));
              todo.push(std::make_pair<TodoTag,TodoVal>(MAIN,
                {.aFla = fl->head()}));
            }
          }
          break;

        case OR:
          {
            int ln = _formulas.length();
            FormulaList::Iterator fs(f->args());
            while (fs.hasNext()) {
              _formulas.push(fs.next());
            }
            todo.push(std::make_pair<TodoTag,TodoVal>(OR_REST,
              {.anInt = ln}));
            todo.push(std::make_pair<TodoTag,TodoVal>(MAIN,
              {.aFla = _formulas.pop()}));
          }
          break;

        case FORALL:
          f = f->qarg();
          goto formula_reset;

        default:
          ASSERTION_VIOLATION;
        }

        break;
      }
      case LIT_REST: {
        Formula* f = task.second.aFla;
        _formulas.push(f);
        _literals.pop();
        break;
      }
      case AND_REST: {
        FormulaList* fl = task.second.aFlist;
        if (FormulaList::isNonEmpty(fl)) {
          todo.push(std::make_pair<TodoTag,TodoVal>(AND_REST,
            {.aFlist = fl->tail()}));
          todo.push(std::make_pair<TodoTag,TodoVal>(MAIN,
            {.aFla = fl->head()}));
        }
        break;
      }
      case OR_REST: {
        int ln = task.second.anInt;
        _formulas.truncate(ln);
        break;
      }
    }
  } while(todo.isNonEmpty());
}

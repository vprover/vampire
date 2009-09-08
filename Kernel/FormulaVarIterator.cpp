/**
 * @file FormulaVarIterator.cpp
 * Implements a class FormulaVarIterator that iterates
 * over free variables in a formula formulas.
 *
 * @since 06/01/2004, Manchester
 * @since 02/09/2009 Redmond, reimplemented to work with non-rectified
 * formulas and return each variable only once
 */

#include "../Debug/Tracer.hpp"

#include "FormulaVarIterator.hpp"
#include "Formula.hpp"
#include "Term.hpp"

using namespace Lib;
using namespace Kernel;

/**
 * Build an iterator over f.
 * @since 02/09/2009 Redmond
 */
FormulaVarIterator::FormulaVarIterator (const Formula* f)
  : _found(false)
{
  _instructions.push(FVI_FORMULA);
  _formulas.push(f);
} // FormulaVarIterator::FormulaVarIterator

/**
 * Return the next free variable.
 * @since 06/01/2004 Manchester
 */
int FormulaVarIterator::next ()
{
  CALL("FormulaVarIterator::next");

  ASS(_found);
  _found = false;
  return _nextVar;
} // FormulaVarIterator::next

/**
 * True if there is the next free variable.
 * @since 06/01/2004 Manchester
 * @since 11/12/2004 Manchester, true and false added
 */
bool FormulaVarIterator::hasNext()
{
  CALL("FormulaVarIterator::hasNext");

  if (_found) return true;
  
  while (! _instructions.isEmpty()) {
    switch (_instructions.pop()) {
    case FVI_FORMULA:
      {
	const Formula* f = _formulas.pop();
	switch (f->connective()) {
	case LITERAL:
	  _instructions.push(FVI_TERM);
	  _terms.push(f->literal()->args());
	  break;

	case AND:
	case OR:
	  {
	    FormulaList::Iterator fs(f->args());
	    while (fs.hasNext()) {
	      _instructions.push(FVI_FORMULA);
	      _formulas.push(fs.next());
	    }
	  }
	  break;

	case IMP:
	case IFF:
	case XOR:
	  _instructions.push(FVI_FORMULA);
	  _formulas.push(f->left());
	  _instructions.push(FVI_FORMULA);
	  _formulas.push(f->right());
	  break;

	case NOT:
	  _instructions.push(FVI_FORMULA);
	  _formulas.push(f->uarg());
	  break;

	case FORALL:
	case EXISTS:
	  {
	    IntList::Iterator vs(f->vars());
	    while (vs.hasNext()) {
	      _bound.inc(vs.next());
	    }
	    _instructions.push(FVI_UNBIND);
	    _formulas.push(f);
	    _instructions.push(FVI_FORMULA);
	    _formulas.push(f->qarg());
	  }
	  break;
	  
	case TRUE:
	case FALSE:
	  break;
	}
      }
      break;
    case FVI_TERM:
      {
	const TermList* ts = _terms.pop();
	if (ts->isEmpty()) break;
	_instructions.push(FVI_TERM);
	_terms.push(ts->next());
	if (ts->isVar()) {
	  unsigned v = ts->var();
	  if (_free.get(v)) continue;
	  if (_bound.get(v)) continue;
	  _nextVar = v;
	  _found = true;
	  _free.inc(v);
	  return true;
	}
	_instructions.push(FVI_TERM);
	_terms.push(ts->term()->args());
      }
      break;
    case FVI_UNBIND:
      {
	const Formula* f = _formulas.pop();
	IntList::Iterator vs(f->vars());
	while (vs.hasNext()) {
	  _bound.dec(vs.next());
	}
      }
      break;
    }
  }
  return false;
} // FormulaVarIterator::hasNext




/**
 * @file FormulaVarIterator.cpp
 * Implements a class FormulaVarIterator that iterates
 * over free variables in a formula formulas.
 *
 * @since 06/01/2004, Manchester
 * @since 02/09/2009 Redmond, reimplemented to work with non-rectified
 * formulas and return each variable only once
 */

#include "Debug/Tracer.hpp"

#include "FormulaVarIterator.hpp"
#include "Formula.hpp"
#include "Term.hpp"
#include "TermIterators.hpp"

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

FormulaVarIterator::FormulaVarIterator (const Term* trm)
  : _found(false)
{
  CALL("FormulaVarIterator::FormulaVarIterator(const Literal*)");
  _instructions.push(FVI_TERM);
  _terms.push(trm->args());
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
	  if(suggestNextVar(v)) {
	    return true;
	  }
	}
	else {
	  const Term* trm = ts->term();
	  if(trm->isSpecial()) {
	    if(processSpecialTerm(ts)) {
	      return true;
	    }
	  }
	  else {
	    _instructions.push(FVI_TERM);
	    _terms.push(trm->args());
	  }
	}
      }
      break;
    case FVI_UNBIND:
      {
	const Formula* f = _formulas.pop();
	Connective con = f->connective();
	ASS(con==EXISTS || con==FORALL)
	IntList::Iterator vs(f->vars());
	while (vs.hasNext()) {
	  _bound.dec(vs.next());
	}
      }
      break;
    case FVI_UNBIND_TERM_LET:
      {
	const TermList* t = _terms.pop();
	countTermLetLhsVars(t->term(), false);
      }
      break;
    }
  }
  return false;
} // FormulaVarIterator::hasNext

/**
 * Process special term @c ts. If variable acceptable as the next variable
 * returned by the iterator is found, make it the next variable and return
 * true. Otherwise return false.
 */
bool FormulaVarIterator::processSpecialTerm(const TermList* ts)
{
  CALL("FormulaVarIterator::processSpecialTerm");

  const Term* t = ts->term();
  ASS(t->isSpecial())

  const Term::SpecialTermData* sd = t->getSpecialData();
  if(t->functor()==Term::SF_TERM_ITE) {
    _instructions.push(FVI_FORMULA);
    _formulas.push(sd->getCondition());
    _instructions.push(FVI_TERM);
    _terms.push(t->args());
  }
  else if(t->functor()==Term::SF_FORMULA) {
	_instructions.push(FVI_FORMULA);
	_formulas.push(sd->getFormula());
  }
  else {
    _instructions.push(FVI_TERM);
    _terms.push(t->args());
    _instructions.push(FVI_UNBIND_TERM_LET);
    _terms.push(ts);
    countTermLetLhsVars(t, true);
    if(t->functor()==Term::SF_LET_FORMULA_IN_TERM) {
      _instructions.push(FVI_FORMULA);
      _formulas.push(sd->getRhsFormula());
    }
    else {
      TermList rhs = sd->getRhsTerm();
      if(rhs.isTerm()) {
	_instructions.push(FVI_TERM);
	_terms.push(rhs.term()->args());
      }
      else {
	if(suggestNextVar(rhs.var())) {
	  return true;
	}
      }
    }
  }
  return false;
}

/**
 * If variable @c v is acceptable as the next variable returned by the iterator,
 * make it the next variable and return true. Otherwise return false.
 */
bool FormulaVarIterator::suggestNextVar(unsigned v)
{
  CALL("FormulaVarIterator::suggestNextVar");

  if (_free.get(v)) return false;
  if (_bound.get(v)) return false;
  _nextVar = v;
  _found = true;
  _free.inc(v);
  return true;
}

/**
 * Add or remove (based on the last arg) variables of LHS of
 * let term @c t.
 */
void FormulaVarIterator::countTermLetLhsVars(const Term* t, bool inc)
{
  CALL("FormulaVarIterator::countTermLetLhsVars");

  static VariableIterator vit;
  const Term::SpecialTermData* sd = t->getSpecialData();
  if(t->functor()==Term::SF_LET_FORMULA_IN_TERM) {
    vit.reset(sd->getLhsLiteral());
  }
  else {
    ASS_EQ(t->functor(),Term::SF_LET_TERM_IN_TERM);
    if(sd->getLhsTerm().isTerm()) {
      vit.reset(sd->getLhsTerm().term());
    }
    else {
      INVALID_OPERATION("Let expressions with variable lhs are currently not handled");
    }
  }
  while(vit.hasNext()) {
    TermList var = vit.next();
    if(inc) {
      _bound.inc(var.var());
    }
    else {
      _bound.dec(var.var());
    }
  }
}

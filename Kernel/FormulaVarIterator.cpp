/**
 * @file FormulaVarIterator.cpp
 * Implements a class FormulaVarIterator that iterates
 * over free variables in a formula formulas.
 *
 * @since 06/01/2004, Manchester
 */

#include "../Debug/Tracer.hpp"

#include "FormulaVarIterator.hpp"
#include "Formula.hpp"
#include "Term.hpp"

using namespace Lib;

namespace Kernel {

/**
 * Implements elements of the iterator. It may contains elements of
 * three types: term lists, formulas, and formula lists
 * @since 06/01/2004, Manchester
 */
class FormulaVarIterator::Element
{
public:
  enum Tag {
    TERMS = 0,
    FORMULA = 1,
    FORMULAS = 2
  };

  Tag _tag;
  union { 
    const FormulaList* _formulas;
    const Formula* _formula;
    const TermList* _terms;
  };
  Element* _rest;

  Element (const FormulaList* fs, Element* rest);
  Element (const TermList* ts, Element* rest);
  Element (const Formula* f, Element* rest);

  CLASS_NAME("FormulaVarIterator::Element");
  USE_ALLOCATOR(FormulaVarIterator::Element);
}; // class FormulaVarIterator::Element


/**
 * Build an iterator over f.
 * @since 06/01/2004 Manchester
 */
FormulaVarIterator::FormulaVarIterator (const Formula* f)
  : _current(0),
    _reserve(new Element(f,0))
{
} // FormulaVarIterator::FormulaVarIterator


/**
 * Create a new element containing a formula list.
 */
FormulaVarIterator::Element::Element (const FormulaList* fs, Element* rest)
  : _tag(FORMULAS),
    _formulas(fs), 
    _rest(rest)
{
} // FormulaVarIterator::Element::Element


/**
 * Create a new element containing a formula.
 */
FormulaVarIterator::Element::Element (const Formula* f, Element* rest)
  : _tag(FORMULA),
    _formula(f), 
    _rest(rest)
{
} // FormulaVarIterator::Element::Element


/**
 * Create a new element containing a term list.
 */
FormulaVarIterator::Element::Element (const TermList* ts, Element* rest)
  : _tag(TERMS),
    _terms(ts), 
    _rest(rest)
{
} // FormulaVarIterator::Element::Element


/**
 * True if there is the next free variable.
 * @since 06/01/2004 Manchester
 * @since 11/12/2004 Manchester, true and false added
 */
bool FormulaVarIterator::hasNext ()
{
  CALL("FormulaVarIterator::hasNext");

  for (;;) {
    if (_current) { // there is a current term
      if (_current->isEmpty()) {
      }
      else if (_current->isVar()) {
	if (_bound.get(_current->var()) == 0) { // variable is free
	  return true;
	}
      }
      else { // current is a reference
	_reserve = new Element(_current->next(),_reserve);
	_current = _current->term()->args();
	continue;
      }
      _current = 0;
    }
    // _current == 0
    if (! _reserve) {
      return false;
    }
    // _current == 0 but _reserve != 0
    switch (_reserve->_tag) {
    case Element::TERMS:
      {
	const TermList* ts = _reserve->_terms;
	if (ts->isEmpty()) {
	  popReserve();
	  break;
	}
	// ts is non-empty
	_current = ts;
	_reserve->_terms = ts->next();
	break;
      }

    case Element::FORMULAS:
      {
	const FormulaList* fs = _reserve->_formulas;
	if (fs->isEmpty()) {
	  popReserve();
	  break;
	}
	// fs is non-empty
	const Formula* first = fs->head();
	_reserve->_formulas = fs->tail();
	_reserve = new Element(first,_reserve);
	break;
      }

    case Element::FORMULA:
      {
	const Formula* f = _reserve->_formula;
	switch (f->connective()) {
	case LITERAL:
	  _reserve->_tag = Element::TERMS;
	  _reserve->_terms = f->literal()->args();
	  break;

	case AND:
	case OR:
	  _reserve->_tag = Element::FORMULAS;
	  _reserve->_formulas = f->args();
	  break;

	case IMP:
	case IFF:
	case XOR:
	  _reserve->_formula = f->right();
	  _reserve = new Element(f->left(),_reserve);
	  break;

	case NOT:
	  _reserve->_formula = f->uarg();
	  break;

	case FORALL:
	case EXISTS:
	  {
	    // first, mark bound variables
	    Formula::VarList::Iterator vs(f->vars());
	    while (vs.hasNext()) {
	      _bound.inc(vs.next());
	    }
	    _reserve->_formula = f->qarg();
	    break;
	  }
	  
	case TRUE:
	case FALSE:
	  popReserve();
	  break;

#if VDEBUG
	default:
	  ASSERTION_VIOLATION;
#endif
	}
	break;
      }
#if VDEBUG
    default:
      ASSERTION_VIOLATION;
#endif
    }
  }
} // FormulaVarIterator::hasNext


/**
 * Remove the first record from _reserve.
 */
void FormulaVarIterator::popReserve ()
{
  CALL("FormulaVarIterator::popReserve()");
  ASS(_reserve);

  Element* next = _reserve->_rest;
  delete _reserve;
  _reserve = next;
} // FormulaVarIterator::popReserve


/**
 * Return the next free variable.
 * @since 06/01/2004 Manchester
 */
int FormulaVarIterator::next ()
{
  CALL("FormulaVarIterator::next");

  ASS(_current);
  int result = _current->var();
  _current = 0;
  return result;
} // FormulaVarIterator::next


/**
 * Destroy the iterator.
 */
FormulaVarIterator::~FormulaVarIterator ()
{
  CALL("FormulaVarIterator::~FormulaVarIterator");

  while (_reserve) {
    Element* next = _reserve->_rest;
    delete _reserve;
    _reserve = next;
  }
} // FormulaVarIterator::~FormulaVarIterator

}

/**
 * @file SubformulaIterator.cpp
 * Implements a class SubformulaIterator that iterates
 * over subformulas in formula lists, and formulas.
 *
 * @since 06/01/2004 Manchester
 * @since 02/06/2007 Manchester changed to new datastructures
 */

#include "Debug/Tracer.hpp"

#include "SubformulaIterator.hpp"

namespace Kernel {

/**
 * Elements strong information, used internally in subformula iterators.
 */
class SubformulaIterator::Element {
public:
  Element (FormulaList* list, Element* rest)
    : _isList(true),
      _list(list),
      _rest(rest)
  {}
  Element (Formula* f, Element* rest)
    : _isList(false),
      _formula(f),
      _rest(rest)
  {}
  bool _isList;
  union{
    FormulaList* _list;
    Formula* _formula;
  };
  Element* _rest;

  CLASS_NAME("SubformulaIterator::Element");
  USE_ALLOCATOR(SubformulaIterator::Element);
};


/**
 * Build an iterator over t.
 * @since 06/01/2004 Manchester
 */
SubformulaIterator::SubformulaIterator (Formula* f)
  : _current(f),
    _reserve(0)
{
} // SubformulaIterator::SubformulaIterator


/**
 * Build an iterator over of ts.
 * @since 06/01/2004 Manchester
 */
SubformulaIterator::SubformulaIterator (FormulaList* ts)
  : _current(0),
    _reserve(new Element(ts,0))
{
} // SubformulaIterator::SubformulaIterator


/**
 * True if there the next subformula.
 * @since 06/01/2004 Manchester
 * @since 22/08/2004 Torrevieja, a bug fixed causing reserve formulas
 *                   to be ignored
 */
bool SubformulaIterator::hasNext ()
{
  CALL("SubformulaIterator::hasNext");

  if (_current) {
    return true;
  }

  // try to set _current
  while (_reserve) {
    if (_reserve->_isList) {
      FormulaList* first = _reserve->_list;
      if (first->isEmpty()) {
	Element* rest = _reserve->_rest;
	delete _reserve;
	_reserve = rest;
      }
      else { // first is non-empty
	_current = first->head();
	_reserve->_list = first->tail();
	return true;
      }
    }
    else { // _reserve is a formula
      _current = _reserve->_formula;
      Element* rest = _reserve->_rest;
      delete _reserve;
      _reserve = rest;
      return true;
    }
  }
  // _reserve is empty
  return false;
} // SubformulaIterator::hasNext


/**
 * Return the next subformula.
 *
 * @since 06/01/2004 Manchester
 * @since 11/12/2004 Manchester, true and false added
 */
Formula* SubformulaIterator::next ()
{
  Formula* result = _current;

  switch (result->connective()) {
  case LITERAL:
  case TRUE:
  case FALSE:
    _current = 0;
    break;

  case AND:
  case OR:
    _reserve = new Element(result->args(),_reserve);
    _current = 0;
    break;

  case IMP:
  case IFF:
  case XOR:
    _current = result->left();
    _reserve = new Element(result->right(),_reserve);
    break;

  case NOT:
    _current = result->uarg();
    break;

  case FORALL:
  case EXISTS:
    _current = result->qarg();
    break;

#if VDEBUG
  default:
    ASSERTION_VIOLATION;
#endif
  }

  return result;
} // SubformulaIterator::next


/**
 * Destroy the iterator.
 */
SubformulaIterator::~SubformulaIterator ()
{
  while (_reserve) {
    Element* next = _reserve->_rest;
    delete _reserve;
    _reserve = next;
  }
} // SubformulaIterator::~SubformulaIterator

}

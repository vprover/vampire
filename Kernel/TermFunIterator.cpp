/**
 * @file TermFunIterator.cpp
 * Implements a class TermFunIterator that iterates
 * over function symbols in terms
 *
 * @since 26/05/2007 Manchester, made from TermVarIterator.cpp
 */

#include "../Debug/Tracer.hpp"

#include "Term.hpp"
#include "TermFunIterator.hpp"

using namespace Kernel;

/**
 * Build an iterator over symbols of t.
 * @since 26/05/2007 Manchester
 */
TermFunIterator::TermFunIterator (const Term* t)
  : _stack(64)
{
  CALL("TermFunIterator::TermFunIterator");

  _hasNext = true;
  _next = t->functor();
  _stack.push(t->args());
} // TermFunIterator::TermFunIterator


/**
 * True if there the next function.
 * @since 26/05/2007 Manchester
 */
bool TermFunIterator::hasNext ()
{
  CALL("TermFunIterator::hasNext");

  if (_hasNext) {
    return true;
  }

  while (_stack.isNonEmpty()) {
    const TermList* ts = _stack.pop();
    if (ts->isEmpty()) {
      continue;
    }
    _stack.push(ts->next());
    if (ts->isVar()) {
      continue;
    }
    _hasNext = true;
    const Term* t = ts->term();
    _next = t->functor();
    _stack.push(t->args());
    return true;
  }
  return false;
} // TermFunIterator::hasNext


/**
 * Return the next symbol.
 * @since 26/05/2007 Manchester
 */
unsigned TermFunIterator::next ()
{
  CALL("TermFunIterator::hasNext");

  ASS(_hasNext);

  _hasNext = false;
  return _next;
} // TermFunIterator::next



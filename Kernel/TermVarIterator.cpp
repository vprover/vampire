/**
 * @file TermVarIterator.cpp
 * Implements a class TermVarIterator that iterates
 * over variables in terms.
 *
 * @since 06/01/2004 Manchester
 */

#include "../Debug/Tracer.hpp"

#include "Term.hpp"
#include "TermVarIterator.hpp"

using namespace Kernel;

/**
 * Build an iterator over variables of t.
 * @since 06/01/2004 Manchester
 * @since 26/05/2007 Manchester, reimplemented
 */
TermVarIterator::TermVarIterator (const TermList* ts)
  : _stack(64)
{
  CALL("TermVarIterator::TermVarIterator");
  _stack.push(ts);
} // TermVarIterator::TermVarIterator


/**
 * True if there the next variable.
 * @since 06/01/2004 Manchester
 * @since 26/05/2007 Manchester, reimplemented for new datastructures
 */
bool TermVarIterator::hasNext ()
{
  CALL("TermVarIterator::hasNext");

  while (_stack.isNonEmpty()) {
    const TermList* ts = _stack.pop();
    if (ts->isEmpty()) {
      continue;
    }
    _stack.push(ts->next());
    if (ts->isVar()) {
      _next = ts->var();
      return true;
    }
    _stack.push(ts->term()->args());
  }
  return false;
} // TermVarIterator::hasNext


/**
 * Return the next variable.
 * @since 06/01/2004 Manchester
 * @since 26/05/2007 Manchester, reimplemented for new datastructures
 */
unsigned TermVarIterator::next ()
{
  CALL("TermVarIterator::hasNext");
  return _next;
} // TermVarIterator::next



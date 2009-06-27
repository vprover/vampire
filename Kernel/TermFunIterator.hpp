/**
 * @file TermFunIterator.hpp
 * Defines a class TermFunIterator that iterates
 * over function symbols in terms
 *
 * @since 26/05/2007 Manchester, made from TermVarIterator.hpp
 */

#ifndef __TermFunIterator__
#define __TermFunIterator__

#include "../Lib/Stack.hpp"
#include "../Lib/VirtualIterator.hpp"

using namespace Lib;

namespace Kernel {

class Term;

/**
 * Implements an iterator over function symbols of a term.
 *
 * Functions are yielded before their subterms.
 * @since 26/05/2007 Manchester, made from class TermVarIterator
 */
class TermFunIterator
: public IteratorCore<unsigned>
{
public:
  TermFunIterator (const Term*);

  bool hasNext();
  unsigned next();
private:
  /** True if the next symbol is found */
  bool _hasNext;
  /** next symbol, previously found */
  unsigned _next;
  /** Stack of term lists (not terms!) */
  Stack<const TermList*> _stack;
}; // class TermFunIterator

}

#endif // __TermFunIterator__


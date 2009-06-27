/**
 * @file TermVarIterator.hpp
 * Defines a class TermVarIterator that iterates
 * over variables in terms, including literals.
 *
 * @since 06/01/2004, Manchester
 */

#ifndef __TermVarIterator__
#define __TermVarIterator__

#include "../Lib/Stack.hpp"
#include "../Lib/VirtualIterator.hpp"

using namespace Lib;

namespace Kernel {

class Term;

/**
 * Implements an iterator over variables of a term term list, or atom.
 * @since 06/01/2004 Manchester
 * @since 26/05/2007 Manchester, reimplemented for different data structures
 */
class TermVarIterator
: public IteratorCore<unsigned>
{
public:
  TermVarIterator (const TermList*);

  bool hasNext ();
  unsigned next ();
private:
  /** True if the next variable is found */
  bool _hasNext;
  /** next variable, previously found */
  unsigned _next;
  /** Stack of term lists (not terms!) */
  Stack<const TermList*> _stack;
}; // class TermVarIterator

}

#endif // __TermVarIterator__


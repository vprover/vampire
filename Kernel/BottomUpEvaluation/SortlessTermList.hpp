/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __BOTTOM_UP_EVALUATION__SORTLESS_TERM_LIST_HPP__
#define __BOTTOM_UP_EVALUATION__SORTLESS_TERM_LIST_HPP__

#include "Kernel/BottomUpEvaluation.hpp"

namespace Lib {

// just wrap a TermList for use in BottomUpChildIter
struct SortlessTermList { TermList inner; };

// identical to BottomUpChildIter<TermList>, except no sort arguments are returned
// useful for e.g. Z3 expressions where we handle these as part of function definitions
template<>
struct BottomUpChildIter<SortlessTermList>
{
  SortlessTermList _self;
  unsigned _idx;

  BottomUpChildIter(SortlessTermList self) : _self(self), _idx(0)
  {
    if(hasNext())
      _idx = self.inner.term()->numTypeArguments();
  }

  SortlessTermList next()
  {
    ASS(hasNext());
    return SortlessTermList { *_self.inner.term()->nthArgument(_idx++) };
  }

  bool hasNext() const
  { return _self.inner.isTerm() && _idx < _self.inner.term()->arity(); }

  unsigned nChildren() const
  { return _self.inner.isVar() ? 0 : _self.inner.term()->arity() - _self.inner.term()->numTypeArguments(); }

  SortlessTermList self() const
  { return _self; }
};

} // namespace Lib

#endif//__BOTTOM_UP_EVALUATION__SORTLESS_TERM_LIST_HPP__

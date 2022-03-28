/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __BOTTOM_UP_EVALUATION__TERM_LIST_HPP__
#define __BOTTOM_UP_EVALUATION__TERM_LIST_HPP__

#include "Kernel/BottomUpEvaluation.hpp"

namespace Lib {

// iterate up through TermLists, ignoring sort arguments
template<>
struct BottomUpChildIter<Kernel::TermList>
{
  Kernel::TermList _self;
  unsigned _idx;

  BottomUpChildIter(Kernel::TermList self) : _self(self), _idx(0)
  {
    if(hasNext())
      _idx = _self.term()->numTypeArguments();
  }

  Kernel::TermList next() 
  {
    ASS(hasNext());
    return *_self.term()->nthArgument(_idx++);
  }

  bool hasNext() const 
  { return _self.isTerm() && _idx < _self.term()->arity(); }

  unsigned nChildren() const 
  { return _self.isVar() ? 0 : _self.term()->arity() - _self.term()->numTypeArguments(); }

  Kernel::TermList self() const 
  { return _self; }
};


} // namespace Lib

#endif//__BOTTOM_UP_EVALUATION__TERM_LIST_HPP__

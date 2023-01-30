/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __BOTTOM_UP_EVALUATION__TYPED_TERM_LIST_HPP__
#define __BOTTOM_UP_EVALUATION__TYPED_TERM_LIST_HPP__

#include "Kernel/SortHelper.hpp"
#include "Kernel/TypedTermList.hpp"
#include "Kernel/BottomUpEvaluation.hpp"
#include "Kernel/Term.hpp"
#include "Forwards.hpp"


namespace Lib {

template<>
struct BottomUpChildIter<Kernel::TypedTermList>
{
  Kernel::TypedTermList _self;
  unsigned      _idx;

  BottomUpChildIter(Kernel::TypedTermList self) : _self(self), _idx(0)
  {}

  Kernel::TypedTermList next() 
  {
    ASS(hasNext());
    auto cur = self().term();
    auto next = cur->termArg(_idx);
    auto sort = Kernel::SortHelper::getTermArgSort(cur, _idx);
    ASS_NEQ(sort, Kernel::AtomicSort::superSort())
    _idx++;
    return Kernel::TypedTermList(next, sort);
  }

  bool hasNext() const 
  { return _self.isTerm() && _idx < _self.term()->numTermArguments(); }

  unsigned nChildren() const 
  { return _self.isVar() ? 0 : _self.term()->numTermArguments(); }

  Kernel::TypedTermList self() const 
  { return _self; }
};

} // namespace Lib


#endif//__BOTTOM_UP_EVALUATION__TYPED_TERM_LIST_HPP__

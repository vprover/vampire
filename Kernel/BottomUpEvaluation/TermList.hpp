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

class TermListEvalWithoutSorts : public Kernel::TermList 
{ public: explicit TermListEvalWithoutSorts(Kernel::TermList t) : Kernel::TermList(t) {} };

// iterate up through TermLists, ignoring sort arguments
template<>
struct BottomUpChildIter<TermListEvalWithoutSorts>
{
  TermListEvalWithoutSorts _self;
  unsigned _idx;

  BottomUpChildIter(TermListEvalWithoutSorts self) : _self(self), _idx(0)
  { }

  TermListEvalWithoutSorts next() 
  {
    ASS(hasNext());
    return TermListEvalWithoutSorts(_self.term()->termArg(_idx++));
  }

  bool hasNext() const 
  { return _self.isTerm() && _idx < _self.term()->numTermArguments(); }

  unsigned nChildren() const 
  { return _self.isVar() ? 0 : _self.term()->numTermArguments(); }

  TermListEvalWithoutSorts self() const 
  { return _self; }
};

class TermListEvalWithSorts    : public Kernel::TermList 
{ public: explicit TermListEvalWithSorts   (Kernel::TermList t) : Kernel::TermList(t) {} };

// iterate up through TermLists, including sort arguments
template<>
struct BottomUpChildIter<TermListEvalWithSorts>
{
  TermListEvalWithSorts _self;
  unsigned _idx;

  BottomUpChildIter(TermListEvalWithSorts self) : _self(self), _idx(0)
  { }

  TermListEvalWithSorts next() 
  {
    ASS(hasNext());
    return TermListEvalWithSorts(_self.term()->termArg(_idx++));
  }

  bool hasNext() const 
  { return _self.isTerm() && _idx < _self.term()->numTermArguments(); }

  unsigned nChildren() const 
  { return _self.isVar() ? 0 : _self.term()->arity(); }

  TermListEvalWithSorts self() const 
  { return _self; }
};


} // namespace Lib

#endif//__BOTTOM_UP_EVALUATION__TERM_LIST_HPP__

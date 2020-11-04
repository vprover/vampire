#ifndef __BOTTOM_UP_EVALUATION__TYPED_TERM_LIST_HPP__
#define __BOTTOM_UP_EVALUATION__TYPED_TERM_LIST_HPP__

#include "Kernel/SortHelper.hpp"
#include "Kernel/BottomUpEvaluation.hpp"


namespace Kernel {
// TODO move to other class
class TypedTermList : public TermList
{
  unsigned _sort;
public:
  TypedTermList(TermList t, unsigned sort) : TermList(t), _sort(sort) {}
  TypedTermList(Term* t) : TypedTermList(TermList(t), SortHelper::getResultSort(t)) {}
  unsigned sort() const { return _sort; }
};

} // namespace Kernel 

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
    auto next = *cur->nthArgument(_idx);
    auto sort = Kernel::SortHelper::getArgSort(cur, _idx);
    _idx++;
    return Kernel::TypedTermList(next, sort);
  }

  bool hasNext() const 
  { return _self.isTerm() && _idx < _self.term()->arity(); }

  unsigned nChildren() const 
  { return _self.isVar() ? 0 : _self.term()->arity(); }

  Kernel::TypedTermList self() const 
  { return _self; }
};

} // namespace Lib


#endif//__BOTTOM_UP_EVALUATION__TYPED_TERM_LIST_HPP__

#ifndef __ARRAY_TRAITS__HPP__
#define __ARRAY_TRAITS__HPP__

#include "Forwards.hpp"
#include "Lib/Environment.hpp"
#include "Kernel/NumTraits.hpp"

namespace Kernel {

template<class Idx, class Item>
struct ArrayTraits 
{
  Idx _idx;
  Item _item;

public:
  ArrayTraits(Idx idx, Item item) 
    : _idx(idx)
    , _item(item)
  {  }


  unsigned sortNumber() const 
  { return env.sorts->addArraySort(_idx.sortNumber(), _item.sortNumber()); }

#define IMPL_ARRAY_TRAITS__INTERPRETED_FUN(fun, interpret, _arity)                                            \
  static constexpr Kernel::Interpretation fun ## I = Interpretation::interpret;                               \
                                                                                                              \
  unsigned fun ## F() const                                                                                   \
  {                                                                                                           \
    auto op = theory->getArrayOperatorType(sortNumber(), fun ## I);                                           \
    return env.signature->getInterpretingSymbol(fun##I, op);                                                  \
  }                                                                                                           \
                                                                                                              \
  Kernel::Term* fun ## T(IMPL_NUM_TRAITS__ARG_DECL(TermList, _arity)) const                                   \
  { return Term::create(fun ## F(), {IMPL_NUM_TRAITS__ARG_EXPR(_arity)}); }                                   \
                                                                                                              \
  TermList fun(IMPL_NUM_TRAITS__ARG_DECL(TermList, _arity)) const                                             \
  { return TermList(fun ## T(IMPL_NUM_TRAITS__ARG_EXPR(_arity))); }                                           \

  IMPL_ARRAY_TRAITS__INTERPRETED_FUN(select, ARRAY_SELECT, 2)
  IMPL_ARRAY_TRAITS__INTERPRETED_FUN(store , ARRAY_STORE , 3)

};

template<class Idx, class Item>
ArrayTraits<Idx, Item> arrayTraits(Idx idx, Item item) 
{ return ArrayTraits<Idx, Item>(idx,item); }



} // namespace Kernel

#endif // __ARRAY_TRAITS__HPP__

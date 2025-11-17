/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __Kernel_TypedTermList__
#define __Kernel_TypedTermList__

#include <tuple>

#include "Term.hpp"
#include "SortHelper.hpp"
#include "Lib/Reflection.hpp"

namespace Kernel {
using SortId = Kernel::TermList;

class TypedTermList : public TermList
{
  SortId _sort;
public:
  SortId sort() const { return _sort; }
  TermList untyped() const { return *this; }
  auto asTuple() const -> decltype(auto) { return std::make_tuple(untyped(), sort()); }
  IMPL_COMPARISONS_FROM_TUPLE(TypedTermList);
  IMPL_HASH_FROM_TUPLE(TypedTermList);


    // TODO get rid of default constructor
  TypedTermList() {}
  TypedTermList(TermList t, SortId sort) : TermList(t), _sort(sort) 
  { 
    // ASS_NEQ(sort, AtomicSort::superSort());
    ASS(!sort.isEmpty())
  }
  TypedTermList(Term* t) : TypedTermList(TermList(t), SortHelper::getResultSort(t)) {}

  friend std::ostream& operator<<(std::ostream& out, TypedTermList const& self) 
  { return out << (TermList const&) self << ": " << self._sort; }
};

} // namespace Kernel 


template<>
struct std::hash<Kernel::TypedTermList> {
  size_t operator()(Kernel::TypedTermList const& t) 
  { return t.defaultHash(); }
};

#endif // __Kernel_TypedTermList__

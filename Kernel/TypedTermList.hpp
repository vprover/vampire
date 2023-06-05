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

#include "Kernel/SortHelper.hpp"

namespace Kernel {
using SortId = Kernel::TermList;

class TypedTermList : public TermList
{
  SortId _sort;
public:
  CLASS_NAME(TypedTermList)

  TypedTermList(TermList t, SortId sort) : TermList(t), _sort(sort) 
  { 
    // TODO we have some use cases where we want to enter a sort
    // with sort SuperSort(). See BoolInstantiation
    // ASS_NEQ(sort, AtomicSort::superSort());
    ASS(!sort.isEmpty())
  }
  TypedTermList(Term* t) : TypedTermList(TermList(t), SortHelper::getResultSort(t)) {}
  SortId sort() const { return _sort; }

  friend std::ostream& operator<<(std::ostream& out, TypedTermList const& self) 
  { return out << (TermList const&) self << ": " << self._sort; }
};

} // namespace Kernel 


#endif // __Kernel_TypedTermList__

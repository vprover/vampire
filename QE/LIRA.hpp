/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __QE_LIRA__
#define __QE_LIRA__


#include "Debug/Assertion.hpp"
#include "Kernel/Formula.hpp"
#include "QE/ElimSet.hpp"

namespace QE {

class LIRA {
public:
  static Stack<ElimSet> computeElimSet(unsigned var, Stack<Literal*> const& conjunction);
  static IterTraits<VirtualIterator<ElimTerm>> iterElimSet(unsigned var, Literal* conjunction);
  static auto iterElimSet(unsigned var, Stack<Literal*> const& conjunction)
  {
    return arrayIter(conjunction)
      .flatMap([var](auto l) { return iterElimSet(var, l); });
  }
};

namespace CDVS {

struct ConflictDrivenVirtualSubstitution {
  static bool decide(Kernel::Formula* f) { ASSERTION_VIOLATION_REP("TODO") }
};

} // namespace CDVS


} // namespace QE

#endif // __QE_LIRA__

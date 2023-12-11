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


#include "QE/ElimSet.hpp"

namespace QE {

class LIRA {
public:
  static Stack<ElimSet> computeElimSet(Stack<Literal*> const& conjunction);
};


} // namespace QE

#endif // __QE_LIRA__

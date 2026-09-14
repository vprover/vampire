/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */


#include "SelectionPrimitves.hpp"
#include "State.hpp"

namespace Kernel  {

SelectedLiteral::SelectedLiteral(Clause* clause, unsigned litIdx, const AlascaState& shared)
  : cl(clause)
  , litIdx(litIdx)
  , interpreted(shared.norm().tryNormalizeInterpreted(literal()))
{}


} // namespace Kernel

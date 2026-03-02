/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file HOLUnifier.cpp
 * Implements class HOLUnifier.
 */

#include "Kernel/Clause.hpp"
#include "Kernel/Term.hpp"

#include "HOLUnifier.hpp"

namespace Saturation {

bool isHOLUnificationConstraint(Literal* lit)
{
  if (!lit->isEquality() || lit->isPositive()) {
    return false;
  }
  return lit->termArg(0).isLambdaTerm() || lit->termArg(1).isLambdaTerm();
}

Clause* HOLUnifier::handleClause(Clause* cl)
{
  for (const auto& lit : *cl) {
    if (isHOLUnificationConstraint(lit)) {
      // TODO
      ASSERTION_VIOLATION;
    }
  }
  return cl;
}

} // namespace Saturation

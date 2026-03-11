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
 * @file FlexFlexSimplify.cpp
 * Implements class FlexFlexSimplify.
 */

#include "Kernel/Inference.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Clause.hpp"
#include "FlexFlexSimplify.hpp"

using namespace Lib;
using namespace Kernel;

namespace Inferences {

Clause* FlexFlexSimplify::simplify(Clause* c)
{
  if (c->isEmpty()) {
    return c;
  }
  if (c->iterLits().any([](auto lit) { return !lit->isEquality() || !lit->isFlexFlexConstraint(); })) {
    return c;
  }
  // all flex-flex, return the empty clause
  return Clause::empty(SimplifyingInference1(InferenceRule::FLEX_FLEX_SIMPLIFY, c));
}

}
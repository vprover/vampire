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
 * @file ArgPruning.hpp
 * Defines class ArgPruning.
 */

#ifndef __ARG_PRUNING__
#define __ARG_PRUNING__

#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"

namespace Inferences {

struct ArgPruning : public ImmediateSimplificationEngine
{
  Clause* simplify(Clause* premise) override;
};

}

#endif

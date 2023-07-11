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
 * @file ChainSimp.hpp
 * Defines class ChainSimp.
 */

#ifndef __CHAIN_SIMP__
#define __CHAIN_SIMP__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

class ChainSimp : public ImmediateSimplificationEngine
{
  public:
    CLASS_NAME(ChainSimp);
    USE_ALLOCATOR(ChainSimp);
    Clause* simplify(Clause* premise);
};

}

#endif

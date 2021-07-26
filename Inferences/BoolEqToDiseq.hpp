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
 * @file BoolSimp.hpp
 * Defines class BoolSimp.
 */

#ifndef __BoolEqToDiseq__
#define __BoolEqToDiseq__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

class BoolEqToDiseq : public GeneratingInferenceEngine
{
  public:
    CLASS_NAME(BoolEqToDiseq);
    USE_ALLOCATOR(BoolEqToDiseq);

    ClauseIterator generateClauses(Clause* premise);

};

}

#endif

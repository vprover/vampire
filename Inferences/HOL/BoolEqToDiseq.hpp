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
 * @file BoolEqToDiseq.hpp
 * Defines class BoolEqToDiseq.
 */

#ifndef __BoolEqToDiseq__
#define __BoolEqToDiseq__

#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"

namespace Inferences {

class BoolEqToDiseq : public GeneratingInferenceEngine
{
  public:
    BoolEqToDiseq(SaturationAlgorithm&) {}
    ClauseIterator generateClauses(Clause* premise) override;
};

}

#endif

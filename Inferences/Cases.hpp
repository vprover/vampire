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
 * @file Cases.hpp
 * Defines class Cases.
 */

#ifndef __Cases__
#define __Cases__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

class Cases
  : public GeneratingInferenceEngine
{
public:
  Cases(SaturationAlgorithm& salg);
  ClauseIterator generateClauses(Clause* premise) override;
private:
  const Ordering& _ord;
};

}

#endif

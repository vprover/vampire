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
 * @file EqualityResolution.hpp
 * Defines class EqualityResolution.
 */


#ifndef __EquationBalancingForLoopCounters__
#define __EquationBalancingForLoopCounters__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class EquationBalancingForLoopCounters
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(EquationBalancingForLoopCounters);
  USE_ALLOCATOR(EquationBalancingForLoopCounters);

  ClauseIterator generateClauses(Clause* premise);
};


};

#endif /* __EquationBalancingForLoopCounters__ */

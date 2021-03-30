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
 * @file Factoring.hpp
 * Defines class Factoring.
 */


#ifndef __Factoring__
#define __Factoring__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class Factoring
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(Factoring);
  USE_ALLOCATOR(Factoring);

  ClauseIterator generateClauses(Clause* premise);
private:
  class UnificationsOnPositiveFn;
  class ResultsFn;
};


};

#endif /* __Factoring__ */

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
 * @file EqualityFactoring.hpp
 * Defines class EqualityFactoring.
 */


#ifndef __EqualityFactoring__
#define __EqualityFactoring__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"
#include "Shell/Options.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class EqualityFactoring
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(EqualityFactoring);
  USE_ALLOCATOR(EqualityFactoring);

  ClauseIterator generateClauses(Clause* premise);
private:
  struct IsPositiveEqualityFn;
  struct IsDifferentPositiveEqualityFn;
  struct FactorablePairsFn;
  struct ResultFn;

};


};

#endif /* __EqualityFactoring__ */

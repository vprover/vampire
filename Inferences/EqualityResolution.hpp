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


#ifndef __EqualityResolution__
#define __EqualityResolution__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"
#include "Shell/Options.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class EqualityResolution
: public GeneratingInferenceEngine
{
  using AbstractingAlgo = UnificationAlgorithms::AbstractingUnification;
  using RobAlgo = UnificationAlgorithms::RobUnification;
  using HOLAlgo = UnificationAlgorithms::HOLUnification;
  
public:
  CLASS_NAME(EqualityResolution);
  USE_ALLOCATOR(EqualityResolution);

  void attach(SaturationAlgorithm* salg);

  ClauseIterator generateClauses(Clause* premise);
  static Clause* tryResolveEquality(Clause* cl, Literal* toResolve);
private:

  template<class UnifAlgo>
  struct ResultFn;
  struct IsNegativeEqualityFn;
};


};

#endif /* __EqualityResolution__ */

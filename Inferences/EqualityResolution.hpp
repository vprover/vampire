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
#include "Inferences/ProofExtra.hpp"
#include "Shell/Options.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class EqualityResolution
: public GeneratingInferenceEngine
{
public:
  ClauseIterator generateClauses(Clause* premise);
  static Clause* tryResolveEquality(Clause* cl, Literal* toResolve);

  /** TODO 2 should we make this a correct estimation */
  virtual VirtualIterator<std::tuple<>> lookaheadResultEstimation(NewSelectedAtom const& selection) override
  { return pvi(dropElementType(range(0,0))); }
private:
  struct ResultFn;
  struct IsNegativeEqualityFn;
};

using EqualityResolutionExtra = LiteralInferenceExtra;

};

#endif /* __EqualityResolution__ */

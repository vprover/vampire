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
 * @file FOOLParamodulation.hpp
 * Defines class FOOLParamodulation.
 */

#ifndef __Cases__
#define __Cases__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

class Cases : public GeneratingInferenceEngine {
  public:
    Clause* performParamodulation(Clause* cl, Literal* lit, TermList t);
    ClauseIterator generateClauses(Clause* premise) override;
    struct RewriteableSubtermsFn;
    struct ResultFn;


  /** TODO 2 should we make this a correct estimation */
  virtual VirtualIterator<std::tuple<>> lookaheadResultEstimation(NewSelectedAtom const& selection) override
  { return pvi(dropElementType(range(0,0))); }
};

}

#endif

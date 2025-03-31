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
  struct PotentialApplicationIters;
  friend struct PotentialApplicationIters;
  public:
    Clause* performParamodulation(Clause* cl, Literal* lit, TermList t);
    ClauseIterator generateClauses(Clause* premise) override;
    struct RewriteableSubtermsFn;
    struct ResultFn;


  virtual VirtualIterator<std::tuple<>> lookaheadResultEstimation(SelectedAtom const& selection) override;
};

}

#endif

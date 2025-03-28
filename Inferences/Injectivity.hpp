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
 * @file Injectivty.hpp
 * Defines class Injectivty.
 */

#ifndef __Injectivity__
#define __Injectivity__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

class Injectivity : public GeneratingInferenceEngine {
  public:
    ClauseIterator generateClauses(Clause* premise) override;

  virtual VirtualIterator<std::tuple<>> lookaheadResultEstimation(SelectedAtom const& selection) override
  { return lookeaheadResultDoesNotDependOnSelection(); }

  private:
  	TermList createNewLhs(TermList oldhead, TermStack& termArgs, unsigned index);
};

}

#endif

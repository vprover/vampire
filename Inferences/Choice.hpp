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
 * @file BoolSimp.hpp
 * Defines class BoolSimp.
 */

#ifndef __CHOICE__
#define __CHOICE__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

class Choice : public GeneratingInferenceEngine
{
  public:
    ClauseIterator generateClauses(Clause* premise) override;

  private:
    struct SubtermsFn;
    struct IsChoiceTerm;
    struct ResultFn;
    struct AxiomsIterator;
    static Clause* createChoiceAxiom(TermList op, TermList set);

  /** TODO 2 should we make this a correct estimation */
  virtual VirtualIterator<std::tuple<>> lookaheadResultEstimation(SelectedAtom const& selection) override
  { return pvi(dropElementType(range(0,0))); }
};

}

#endif

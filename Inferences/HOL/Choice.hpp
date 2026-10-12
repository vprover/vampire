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
 * @file Choice.hpp
 * Defines class Choice.
 */

#ifndef __CHOICE__
#define __CHOICE__

#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"

namespace Inferences {

class Choice : public GeneratingInferenceEngine
{
  public:
    Choice(SaturationAlgorithm&) {}
    ClauseIterator generateClauses(Clause* premise) override;
    /** Shared axiom construction for search and parentless proof replay. */
    static Clause* createChoiceAxiom(TermList op, TermList set);

  private:
    struct IsChoiceTerm;
    struct ResultFn;
    struct AxiomsIterator;
};

}

#endif

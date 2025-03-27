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

#ifndef __ElimLeibniz__
#define __ElimLeibniz__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"
#include "Kernel/RobSubstitution.hpp"

namespace Inferences {

class ElimLeibniz : public GeneratingInferenceEngine
{
  public:
    ClauseIterator generateClauses(Clause* premise);

    /** TODO 2 should we make this a correct estimation */
    virtual VirtualIterator<std::tuple<>> lookaheadResultEstimation(NewSelectedAtom const& selection) override
    { return pvi(dropElementType(range(0,0))); }

  private:

    struct LeibEqRec {
      unsigned var;

      TermList argSort;
      TermList arg;
    };

    bool polarity(Literal* lit);

    bool isPair(Literal* l1, Literal* l2);

    Clause* createConclusion(Clause* premise, Literal* newLit, Literal* posLit, Literal* negLit, RobSubstitution& subst);

    LeibEqRec getLiteralInfo(Literal* lit);

};

}

#endif

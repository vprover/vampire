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

#ifndef __ChainReasoning__
#define __ChainReasoning__

#include "Forwards.hpp"
#include "Indexing/TermIndex.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

class ChainReasoning : public GeneratingInferenceEngine {
  public:
    CLASS_NAME(ChainReasoning);
    USE_ALLOCATOR(ChainReasoning);
    
    ClauseIterator generateClauses(Clause* premise);

    void attach(SaturationAlgorithm* salg);
    void detach();

  private:
    ChainReasoningChainTermIndex* _chainIndex;
    ChainReasoningLengthClauseIndex* _boundIndex;
    // used to connect locations to chains for chains that are equal to null
    // for example, if C = chain(loc, tp, len) = null, then
    // loc -> chain(...) inserted into map
    DHSet<Term*> _chainTerms;
    DHMap<Term*, Clause*> _chainClauses;

};

}

#endif

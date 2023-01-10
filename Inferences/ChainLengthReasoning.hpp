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


#ifndef __ChainLengthReasoning__
#define __ChainLengthReasoning__

#include "Forwards.hpp"
#include "Indexing/TermIndex.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class ChainLengthReasoning
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(ChainLengthReasoning);
  USE_ALLOCATOR(ChainLengthReasoning);
  
  // reason about chain lengths
  // if we have a chains a ->n tp null 
  // and                 a ->m tp null
  // then n = m

  ClauseIterator generateClauses(Clause* premise);

  void attach(SaturationAlgorithm* salg);
  void detach();

private:
  Clause* createResult(Clause* queuryC, Literal* queryLit, TermList queryChain, TermList loc, TermList tp, TermList len, TermQueryResult& tqr);

  NullTerminatedChainIndex* _index;  
};


};

#endif /* __ChainLengthReasoning__ */

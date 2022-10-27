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


#ifndef __PointerChaining__
#define __PointerChaining__

#include "Forwards.hpp"
#include "Indexing/TermIndex.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class PointerChaining
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(PointerChaining);
  USE_ALLOCATOR(PointerChaining);
  
  // a basic form transitivity for pointer chains
  // a ->*n b && b -> c  ===> a ->*(n+1) c
  // a -> b   && b -> c  ===> a ->*2     c
 
  ClauseIterator generateClauses(Clause* premise);

  void attach(SaturationAlgorithm* salg);
  void detach();

private:
  Clause* createResult(TermList queryEnd, TermList len, TermList tp, bool right, TermQueryResult& tqr, Clause* premise);

  PointerChainRhsIndex* _rhsIndex;
  PointerChainLhsIndex* _lhsIndex;  
};


};

#endif /* __PointerChaining__ */

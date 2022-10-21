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


#ifndef __UnitInequalityChaining__
#define __UnitInequalityChaining__

#include "Forwards.hpp"
#include "Indexing/TermIndex.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class UnitInequalityChaining
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(UnitInequalityChaining);
  USE_ALLOCATOR(UnitInequalityChaining);
  
  // a basic form transitivity for inequalities
  // given unit equalitites (a </<= b) and (s </<= t)
  // produces (a </<= t)\sigma where \sigma is unifier
  // of b and s

  ClauseIterator generateClauses(Clause* premise);

  void attach(SaturationAlgorithm* salg);
  void detach();

private:
  Clause* createResult(Literal* lit, TermList trm, bool right, TermQueryResult& tqr, Clause* premise);

  UnitInequalityRhsIndex* _rhsIndex;
  UnitInequalityLhsIndex* _lhsIndex;  
};


};

#endif /* __UnitInequalityChaining__ */

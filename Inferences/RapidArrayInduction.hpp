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
 * @file PrimitiveInstantiation.hpp
 * Defines class PrimitiveInstantiation.
 */


#ifndef __RapidArrayInduction__
#define __RapidArrayInduction__

#include "Forwards.hpp"
#include "Indexing/TermIndex.hpp"

#include "Kernel/FormulaTransformer.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class RapidArrayInduction
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(RapidArrayInduction);
  USE_ALLOCATOR(RapidArrayInduction);
 
  void attach(SaturationAlgorithm* salg);
  void detach();

  ClauseIterator generateClauses(Clause* premise);
  
private:
  void createConclusions(ClauseStack& conclusions, bool increasing, Literal* subLit,
  TermList freshVar, TermList arrayAtNextIt, TermList concRHS,
  TermList index, TermList indexAtNextIter);

  RapidDensityClauseIndex* _densityIndex;  
  RapidArrayIndex* _arrayIndex;  

};


};

#endif /* __RapidArrayInduction__ */

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
 * @file BoolInstantiation.hpp
 * Defines class BoolInstantiation.
 */


#ifndef __BoolInstantiation__
#define __BoolInstantiation__

#if VHOL

#include "Forwards.hpp"
#include "Indexing/TermIndex.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class BoolInstantiation
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(BoolInstantiation);
  USE_ALLOCATOR(BoolInstantiation);

  ClauseIterator generateClauses(Clause* premise) override;

  void attach(SaturationAlgorithm* salg) override;
  void detach() override;   

private:
  Set<TermList> _insertedInstantiations;  
  BoolInstFormulaIndex*  _boolInstFormIndex;
};


};

#endif

#endif /* __BoolInstantiation__ */

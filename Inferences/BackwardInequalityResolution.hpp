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
 * @file BackwardInequalityResolution.hpp
 * Defines class BackwardInequalityResolution.
 */


#ifndef __BackwardInequalityResolution__
#define __BackwardInequalityResolution__

#include "Forwards.hpp"
#include "Indexing/TermIndex.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

using namespace Indexing;
using namespace Kernel;

class BackwardInequalityResolution
: public BackwardSimplificationEngine
{
public:
  CLASS_NAME(BackwardInequalityResolution);
  USE_ALLOCATOR(BackwardInequalityResolution);

  void attach(SaturationAlgorithm* salg);
  void detach();

  void perform(Clause* premise, BwSimplificationRecordIterator& simplifications);

private:
  struct RemovedIsNonzeroFn;
  struct ResultFn;

  InequalityResolutionNonUnitIndex* _index;
};

};

#endif /* __BackwardInequalityResolution__ */
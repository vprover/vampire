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
 * @file SLQueryBackwardSubsumption.hpp
 * Defines class SLQueryBackwardSubsumption.
 */


#ifndef __BackwardDemodulation__
#define __BackwardDemodulation__

#include "Forwards.hpp"
#include "Indexing/TermIndex.hpp"

#include "DemodulationHelper.hpp"
#include "InferenceEngine.hpp"
#include "ProofExtra.hpp"

namespace Inferences {

using namespace Indexing;
using namespace Kernel;

class BackwardDemodulation
: public BackwardSimplificationEngine
{
public:
  void attach(SaturationAlgorithm* salg);
  void detach();

  void perform(Clause* premise, BwSimplificationRecordIterator& simplifications);
private:
  struct RemovedIsNonzeroFn;
  struct RewritableClausesFn;
  struct ResultFn;

  DemodulationSubtermIndex* _index;
  DemodulationHelper _helper;
};

using BackwardDemodulationExtra = RewriteInferenceExtra;
};

#endif /* __BackwardDemodulation__ */

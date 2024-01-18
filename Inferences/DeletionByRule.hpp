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
 * @file DeletionByRule.hpp
 * Defines class DeletionByRule.
 */


#ifndef __DeletionByRule__
#define __DeletionByRule__

#include "Forwards.hpp"
#include "InferenceEngine.hpp"

#include "Indexing/TermIndex.hpp"

namespace Inferences {

class ForwardDeletionByRule
: public ForwardSimplificationEngine
{
public:
  USE_ALLOCATOR(ForwardDeletionByRule);

  void attach(SaturationAlgorithm* salg) override;
  void detach() override;

  bool perform(Clause* cl, Clause*& replacement, ClauseIterator& premises) override;

private:
  Indexing::DemodulationLHSIndex* _index;
};

class BackwardDeletionByRule
: public BackwardSimplificationEngine
{
public:
  USE_ALLOCATOR(BackwardDeletionByRule);

  void attach(SaturationAlgorithm* salg);
  void detach();

  void perform(Clause* premise, BwSimplificationRecordIterator& simplifications);

private:
  Indexing::BlockedTermIndex* _index;
};

};

#endif /* __DeletionByRule__ */

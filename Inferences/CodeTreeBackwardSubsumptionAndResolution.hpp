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
 * @file CodeTreeBackwardSubsumptionAndResolution.hpp
 * Defines class CodeTreeBackwardSubsumptionAndResolution.
 */

#ifndef __CodeTreeBackwardSubsumptionAndResolution__
#define __CodeTreeBackwardSubsumptionAndResolution__

#include "Indexing/LiteralIndex.hpp"
#include "Inferences/InferenceEngine.hpp"
#include "Indexing/CodeTreeInterfaces.hpp"
#if VDEBUG
#include "SATSubsumption/SATSubsumptionAndResolution.hpp"
#endif

namespace Inferences {

template<bool higherOrder>
class CodeTreeBackwardSubsumptionAndResolution
  : public BackwardSimplificationEngine
{
public:
  CodeTreeBackwardSubsumptionAndResolution(SaturationAlgorithm& salg);

  void perform(Clause* premise, BwSimplificationRecordIterator& simplifications) override;

private:
  const bool _subsumptionResolution;
  std::shared_ptr<Indexing::BackwardSubsumptionIndex> _index;
  Indexing::ClauseCodeTree<higherOrder> _ct;
  Lib::DHSet<unsigned> _checked;
#if VDEBUG
  SATSubsumption::SATSubsumptionAndResolution satSubs;
#endif
};

}; // namespace Inferences

#endif /* __CodeTreeBackwardSubsumptionAndResolution__ */

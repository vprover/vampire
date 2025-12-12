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
 * @file CodeTreeForwardSubsumptionAndResolution.hpp
 * Defines class CodeTreeForwardSubsumptionAndResolution.
 */

#ifndef __CodeTreeForwardSubsumptionAndResolution__
#define __CodeTreeForwardSubsumptionAndResolution__

#include "Inferences/InferenceEngine.hpp"
#include "Indexing/CodeTreeInterfaces.hpp"
#if VDEBUG
#include "SATSubsumption/SATSubsumptionAndResolution.hpp"
#endif

namespace Inferences {

class CodeTreeForwardSubsumptionAndResolution
  : public ForwardSimplificationEngine
{
public:
  CodeTreeForwardSubsumptionAndResolution(bool subsumptionResolution) : _subsumptionResolution(subsumptionResolution) {}

  void attach(Saturation::SaturationAlgorithm *salg) override;
  void detach() override;

  bool perform(Kernel::Clause *cl,
               Kernel::Clause *&replacement,
               Kernel::ClauseIterator &premises) override;

private:
  bool _subsumptionResolution;
  Indexing::CodeTreeSubsumptionIndex* _index;
  Indexing::ClauseCodeTree* _ct;
#if VDEBUG
  SATSubsumption::SATSubsumptionAndResolution satSubs;
#endif
};

}; // namespace Inferences

#endif /* __CodeTreeForwardSubsumptionAndResolution__ */

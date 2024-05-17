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
 * @file BackwardSubsumptionAndResolution.hpp
 * Defines class BackwardSubsumptionAndResolution.
 */

#ifndef __BackwardSubsumptionAndResolution__
#define __BackwardSubsumptionAndResolution__

#include "Lib/DHSet.hpp"
#include "InferenceEngine.hpp"
#include "Indexing/LiteralIndex.hpp"
#include "SATSubsumption/SATSubsumptionAndResolution.hpp"

namespace Inferences {

class BackwardSubsumptionAndResolution
    : public BackwardSimplificationEngine {

public:
  USE_ALLOCATOR(BackwardSubsumptionAndResolution);

  BackwardSubsumptionAndResolution(bool subsumption, bool subsumptionByUnitsOnly, bool subsumptionResolution, bool srByUnitsOnly) : _subsumption(subsumption), _subsumptionResolution(subsumptionResolution), _subsumptionByUnitsOnly(subsumptionByUnitsOnly), _srByUnitsOnly(srByUnitsOnly)
  {
    // do nothing
  }
  ~BackwardSubsumptionAndResolution() {}

  void attach(Saturation::SaturationAlgorithm *salg) override;
  void detach() override;
  void perform(Kernel::Clause *premise, Inferences::BwSimplificationRecordIterator &simplifications) override;

  static Kernel::Clause *generateSubsumptionResolutionClause(Kernel::Clause *cl, Kernel::Literal *lit, Kernel::Clause *baseClause);

private:
  bool _subsumption;
  bool _subsumptionResolution;
  bool _subsumptionByUnitsOnly;
  bool _srByUnitsOnly;

  Indexing::BackwardSubsumptionIndex *_bwIndex;
  SATSubsumption::SATSubsumptionAndResolution satSubs;
  Lib::DHSet<Clause *> _checked;

};

}; // namespace Inferences

#endif /* __BackwardSubsumptionAndResolution__ */

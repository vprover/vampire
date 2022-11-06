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

#include "InferenceEngine.hpp"
#include "SATSubsumption/SATSubsumptionResolution.hpp"
#include "Indexing/LiteralMiniIndex.hpp"
#include "Lib/STL.hpp"

#if VDEBUG
#define CHECK_CORRECTNESS_BACKWARD_SUBSUMPTION_AND_RESOLUTION 1
#else
#define CHECK_CORRECTNESS_BACKWARD_SUBSUMPTION_AND_RESOLUTION 0
#endif

#if CHECK_CORRECTNESS_BACKWARD_SUBSUMPTION_AND_RESOLUTION
#include "BackwardSubsumptionResolution.hpp"
#include "SLQueryBackwardSubsumption.hpp"
#endif

namespace Inferences {

class BackwardSubsumptionAndResolution
    : public BackwardSimplificationEngine {

public:
  CLASS_NAME(BackwardSubsumptionAndResolution);
  USE_ALLOCATOR(BackwardSubsumptionAndResolution);

  BackwardSubsumptionAndResolution(bool subsumption, bool subsumptionByUnitsOnly, bool subsumptionResolution, bool srByUnitsOnly) : _subsumption(subsumption), _subsumptionResolution(subsumptionResolution), _subsumptionByUnitsOnly(subsumptionByUnitsOnly), _srByUnitsOnly(srByUnitsOnly),
#if CHECK_CORRECTNESS_BACKWARD_SUBSUMPTION_AND_RESOLUTION
        _index(nullptr), _slqbs(subsumptionByUnitsOnly), _bsr(srByUnitsOnly)
#else
        _index(nullptr)
#endif
  {
    // do nothing
  }
  ~BackwardSubsumptionAndResolution() {}

  void attach(SaturationAlgorithm *salg) override;
  void detach() override;
  void perform(Kernel::Clause *premise, BwSimplificationRecordIterator &simplifications);

  static Kernel::Clause *generateSubsumptionResolutionClause(Kernel::Clause *cl, Kernel::Literal *lit, Kernel::Clause *baseClause);

  static void printStats(std::ostream &out);

private:
  bool _subsumption;
  bool _subsumptionResolution;
  bool _subsumptionByUnitsOnly;
  bool _srByUnitsOnly;

  BackwardSubsumptionIndex *_index;
  SMTSubsumption::SATSubsumption satSubs;
  Lib::DHSet<Clause *> _checked;

#if CHECK_CORRECTNESS_BACKWARD_SUBSUMPTION_AND_RESOLUTION
  SLQueryBackwardSubsumption _slqbs;
  BackwardSubsumptionResolution _bsr;
#endif
};

}; // namespace Inferences

#endif /* __BackwardSubsumptionAndResolution__ */

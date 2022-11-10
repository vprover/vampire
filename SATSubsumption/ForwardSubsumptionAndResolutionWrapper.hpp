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
 * @file ForwardSubsumptionAndResolution.hpp
 * Defines class ForwardSubsumptionAndResolution.
 */

#ifndef __ForwardSubsumptionAndResolutionWrapper__
#define __ForwardSubsumptionAndResolutionWrapper__

#include "Inferences/InferenceEngine.hpp"
#include "SATSubsumption/SATSubsumptionAndResolution.hpp"
#include "Inferences/ForwardSubsumptionAndResolution.hpp"
#include "SATSubsumption/ForwardOracle.hpp"

#include <iostream>
#include <fstream>
#include <chrono>

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

/**
 * Class used to wrap around forward subsumption and resolution inference,
 * compute some time statistics and ensure consistent branching by using
 * the same oracle for each variant of the algorithm.
 */
class ForwardSubsumptionAndResolutionWrapper
    : public ForwardSimplificationEngine {
public:
  CLASS_NAME(ForwardSubsumptionAndResolutionWrapper);
  USE_ALLOCATOR(ForwardSubsumptionAndResolutionWrapper);

  ForwardSubsumptionAndResolutionWrapper(bool subsumptionResolution = true);
  ~ForwardSubsumptionAndResolutionWrapper();

  void attach(Saturation::SaturationAlgorithm *salg) override;
  void detach() override;
  bool perform(Kernel::Clause *cl, Kernel::Clause *&replacement, Kernel::ClauseIterator &premises) override;

  static void printStats(std::ostream &out);

private:
  /** Simplification unit index */
  Indexing::UnitClauseLiteralIndex *_unitIndex;
  Indexing::FwSubsSimplifyingLiteralIndex *_fwIndex;

  Inferences::ForwardSubsumptionAndResolution _forwardSubsumptionAndResolution;
  Inferences::ForwardOracle _forwardOracle;

  bool _subsumptionResolution;
};


}; // namespace Inferences

#endif /* __ForwardSubsumptionAndResolutionWrapper__ */

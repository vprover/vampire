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
 * @file ForwardBenchmark.hpp
 * Defines class ForwardBenchmark.
 */

#ifndef __Forward_Benchmark_Wrapper_PP__
#define __Forward_Benchmark_Wrapper_PP__

#include "Inferences/InferenceEngine.hpp"
#include "SATSubsumption/SATSubsumptionAndResolution.hpp"
#include "SATSubsumption/ForwardBenchmark.hpp"
#include "Inferences/ForwardSubsumptionAndResolution.hpp"

#include <iostream>
#include <fstream>
#include <chrono>

namespace Inferences {

/**
 * Class used to wrap around forward subsumption and resolution inference,
 * compute some time statistics and ensure consistent branching by using
 * the same oracle for each variant of the algorithm.
 */
class ForwardBenchmarkWrapper
    : public ForwardSimplificationEngine {
public:
  CLASS_NAME(ForwardBenchmarkWrapper);
  USE_ALLOCATOR(ForwardBenchmarkWrapper);

  ForwardBenchmarkWrapper(bool subsumptionResolution = true);
  ~ForwardBenchmarkWrapper();

  void attach(Saturation::SaturationAlgorithm *salg) override;
  void detach() override;
  bool perform(Kernel::Clause *cl, Kernel::Clause *&replacement, Kernel::ClauseIterator &premises) override;

  static void printStats(std::ostream &out);

private:
  /** Simplification unit index */
  Indexing::UnitClauseLiteralIndex *_unitIndex;
  Indexing::FwSubsSimplifyingLiteralIndex *_fwIndex;

  Inferences::ForwardBenchmark _forwardBenchmark;
  Inferences::ForwardSubsumptionAndResolution _forwardOracle;

  bool _subsumptionResolution;
};


}; // namespace Inferences

#endif /* __Forward_Benchmark_Wrapper_PP__ */

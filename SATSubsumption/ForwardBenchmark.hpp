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

#ifndef __Forward_Benchmark_HPP__
#define __Forward_Benchmark_HPP__

#include "Inferences/InferenceEngine.hpp"
#include "Inferences/ForwardSubsumptionAndResolution.hpp"
#include "SATSubsumption/SATSubsumptionAndResolution.hpp"
#include "SATSubsumption/SATSubsumptionConfig.hpp"
#include "Indexing/LiteralMiniIndex.hpp"
#include "Lib/STL.hpp"

namespace Inferences {
class ForwardBenchmark
    : public ForwardSimplificationEngine {

  friend class ForwardBenchmarkWrapper;

private:
  bool _subsumptionResolution;

#if SAT_SR_IMPL != 0
  Inferences::ForwardSubsumptionAndResolution _forward;
#else
  /** Simplification unit index */
  Indexing::UnitClauseLiteralIndex *_unitIndex;
  Indexing::FwSubsSimplifyingLiteralIndex *_fwIndex;
  static Clause* generateSubsumptionResolutionClause(Clause* cl, Literal* lit, Clause* baseClause);
#endif

public:
  ForwardBenchmark(bool subsumptionResolution = true, bool log = false)
      : _subsumptionResolution(subsumptionResolution)
#if SAT_SR_IMPL != 0
      , _forward(subsumptionResolution, log)
#endif
  { }

  void attach(Saturation::SaturationAlgorithm *salg) override;
  void detach() override;

  /**
   * Checks whether the clause @b cl can be subsumed or resolved and subsumed by any clause is @b premises .
   * If the clause is subsumed, returns true
   * If the clause is resolved and subsumed, returns true and sets @b replacement to the conclusion clause
   * If the clause is not subsumed or resolved and subsumed, returns false
   *
   * @param cl the clause to check
   * @param replacement the replacement clause if the clause is resolved and subsumed
   * @param premises the premise that successfully subsumed or resolved and subsumed @b cl
   * @return true if the clause is subsumed or resolved and subsumed, false otherwise
   */
  bool perform(Kernel::Clause *cl, Kernel::Clause *&replacement, Kernel::ClauseIterator &premises) override;
};

}; // namespace Inferences

#endif /* __Forward_Benchmark_HPP__ */

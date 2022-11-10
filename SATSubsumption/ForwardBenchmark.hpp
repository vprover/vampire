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
#include "SATSubsumption/SATSubsumptionAndResolution.hpp"
#include "SATSubsumption/SATSubsumptionConfig.hpp"
#include "Indexing/LiteralMiniIndex.hpp"
#include "Lib/STL.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class ForwardBenchmark
    : public ForwardSimplificationEngine {
public:
  CLASS_NAME(ForwardBenchmark);
  USE_ALLOCATOR(ForwardBenchmark);

  ForwardBenchmark(bool subsumptionResolution = true);
  ~ForwardBenchmark();

  void attach(SaturationAlgorithm *salg) override;
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
  bool perform(Clause *cl, Clause *&replacement, ClauseIterator &premises) override;

  static Clause *generateSubsumptionResolutionClause(Clause *cl, Literal *lit, Clause *baseClause);

  static void printStats(std::ostream &out);

private:
  /** Simplification unit index */
  Indexing::UnitClauseLiteralIndex *_unitIndex;
  Indexing::FwSubsSimplifyingLiteralIndex *_fwIndex;

  bool _subsumptionResolution;

#if USE_SAT_SUBSUMPTION_FORWARD || USE_SAT_SUBSUMPTION_RESOLUTION_FORWARD
  SATSubsumption::SATSubsumptionAndResolution satSubs;

#if USE_OPTIMIZED_FORWARD
  Lib::DHSet<Clause *> _checked;
#endif
  Kernel::Clause *_conclusion = nullptr;
  bool _subsumes = false;
  Kernel::Clause *_premise = nullptr;
#endif

#if !USE_SAT_SUBSUMPTION_FORWARD
  bool checkSubsumption(Kernel::Clause *mcl,
                        Kernel::ClauseIterator &premises,
                        Indexing::LiteralMiniIndex &miniIndex);
#elif !USE_OPTIMIZED_FORWARD
  bool checkSubsumption(Kernel::Clause *cl);
#endif

#if !USE_SAT_SUBSUMPTION_RESOLUTION_FORWARD
  Clause *checkSubsumptionResolution(Kernel::Clause *cl,
                                     Kernel::ClauseIterator &premises,
                                     Indexing::LiteralMiniIndex &miniIndex);
#elif !USE_OPTIMIZED_FORWARD
  Clause *checkSubsumptionResolution(Kernel::Clause *cl);
#endif
};

}; // namespace Inferences

#endif /* __Forward_Benchmark_HPP__ */

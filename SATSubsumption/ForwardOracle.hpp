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
 * @file ForwardOracle.hpp
 * Defines class ForwardOracle.
 */

#ifndef __ForwardOracle__
#define __ForwardOracle__

#include "Inferences/InferenceEngine.hpp"
#include "SATSubsumption/SATSubsumptionAndResolution.hpp"
#include "Indexing/LiteralMiniIndex.hpp"
#include "Lib/STL.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class ForwardOracle
    : public ForwardSimplificationEngine {
public:
  CLASS_NAME(ForwardOracle);
  USE_ALLOCATOR(ForwardOracle);

  ForwardOracle(bool subsumptionResolution = true);
  ~ForwardOracle();

  void attach(Saturation::SaturationAlgorithm *salg) override;

  void detach() override;

  bool perform(Kernel::Clause *cl,
               Kernel::Clause *&replacement,
               Kernel::ClauseIterator &premises) override;

  static Kernel::Clause *generateSubsumptionResolutionClause(Kernel::Clause *cl,
                                                             Kernel::Literal *lit,
                                                             Kernel::Clause *baseClause);

  static void printStats(std::ostream &out);

private:
  /** Simplification unit index */
  Indexing::UnitClauseLiteralIndex *_unitIndex;
  Indexing::FwSubsSimplifyingLiteralIndex *_fwIndex;

  bool _subsumptionResolution;

  SATSubsumption::SATSubsumptionAndResolution satSubs;
  Lib::DHSet<Clause *> _checked;
  Kernel::Clause *_conclusion = nullptr;
  bool _subsumes = false;
  Kernel::Clause *_premise = nullptr;
};

}; // namespace Inferences

#endif /* __ForwardOracle__ */

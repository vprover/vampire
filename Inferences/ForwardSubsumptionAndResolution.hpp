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

#ifndef __ForwardSubsumptionAndResolution__
#define __ForwardSubsumptionAndResolution__

#include "Forwards.hpp"
#include "InferenceEngine.hpp"
#include "SATSubsumption/SATSubsumptionAndResolution.hpp"
#include "Indexing/LiteralMiniIndex.hpp"
#include "Lib/STL.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

#if VDEBUG
#define CHECK_SAT_SUBSUMPTION 1
#define CHECK_SAT_SUBSUMPTION_RESOLUTION 1
#else
#define CHECK_SAT_SUBSUMPTION 0
#define CHECK_SAT_SUBSUMPTION_RESOLUTION 0
#endif

#define USE_SAT_SUBSUMPTION_FORWARD 1
#define SEPARATE_LOOPS_FORWARD 0

class ForwardSubsumptionAndResolution
    : public ForwardSimplificationEngine {
public:
  CLASS_NAME(ForwardSubsumptionAndResolution);
  USE_ALLOCATOR(ForwardSubsumptionAndResolution);

  ForwardSubsumptionAndResolution(bool subsumptionResolution = true);
  ~ForwardSubsumptionAndResolution();

  void attach(SaturationAlgorithm *salg) override;
  void detach() override;
  bool perform(Clause *cl, Clause *&replacement, ClauseIterator &premises) override;

  static Clause *generateSubsumptionResolutionClause(Clause *cl, Literal *lit, Clause *baseClause);

  static void printStats(std::ostream &out);

private:
  /** Simplification unit index */
  UnitClauseLiteralIndex *_unitIndex;
  FwSubsSimplifyingLiteralIndex *_fwIndex;

  bool _subsumptionResolution;

#if USE_SAT_SUBSUMPTION_FORWARD
  SATSubsumption::SATSubsumptionAndResolution satSubs;
  DHSet<Clause *> _checked;
  Clause* _conclusion = nullptr;
  bool _subsumes = false;
  Clause* _premise = nullptr;
#endif

#if CHECK_SAT_SUBSUMPTION || !USE_SAT_SUBSUMPTION_FORWARD
  bool checkSubsumption(Clause *mcl, ClauseIterator &premises, LiteralMiniIndex &miniIndex);
#endif
#if CHECK_SAT_SUBSUMPTION_RESOLUTION || !USE_SAT_SUBSUMPTION_FORWARD
  Clause *checkSubsumptionResolution(Clause *cl, ClauseIterator &premises, LiteralMiniIndex &miniIndex);
#endif

};

}; // namespace Inferences

#endif /* __ForwardSubsumptionAndResolution__ */

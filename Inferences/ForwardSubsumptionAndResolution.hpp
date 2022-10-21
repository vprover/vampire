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
#include "SATSubsumption/SATSubsumptionResolution.hpp"
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

#define USE_SAT_SUBSUMPTION 1

class ForwardSubsumptionAndResolution
    : public ForwardSimplificationEngine {
  struct SubsumptionInstance {
    SubsumptionInstance(Clause *L, Clause *M, bool result)
        : _L(L), _M(M), _result(result)
    {
    }
    Clause *_L;
    Clause *_M;
    bool _result;
  };

  struct SubsumptionResolutionInstance {
    SubsumptionResolutionInstance(Clause *L, Clause *M, Clause *conclusion)
        : _L(L), _M(M), _conclusion(conclusion)
    {
    }
    Clause *_L;
    Clause *_M;
    Clause *_conclusion;
  };

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

  SMTSubsumption::SATSubsumption satSubs;

  vvector<SubsumptionInstance> subsumption_tried;
  vvector<SubsumptionResolutionInstance> subsumptionResolution_tried;

#if CHECK_SAT_SUBSUMPTION || !USE_SAT_SUBSUMPTION
  bool checkSubsumption(Clause *mcl, ClauseIterator &premises, LiteralMiniIndex &miniIndex);
#endif
#if CHECK_SAT_SUBSUMPTION_RESOLUTION || !USE_SAT_SUBSUMPTION
  Clause *checkSubsumptionResolution(Clause *cl, ClauseIterator &premises, LiteralMiniIndex &miniIndex);
#endif
};

}; // namespace Inferences

#endif /* __ForwardSubsumptionAndResolution__ */

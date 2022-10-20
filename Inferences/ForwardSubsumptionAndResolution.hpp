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


class ForwardSubsumptionAndResolution
: public ForwardSimplificationEngine
{
    struct SubsumptionInstance
  {
    SubsumptionInstance(Clause* L, Clause* M, bool result)
    : _L(L), _M(M), _result(result)
    {
    }
    Clause * _L;
    Clause * _M;
    bool _result;
  };

  struct SubsumptionResolutionInstance
  {
    SubsumptionResolutionInstance(Clause* L, Clause* M, Clause* conclusion)
    : _L(L), _M(M), _conclusion(conclusion)
    {
    }
    Clause * _L;
    Clause * _M;
    Clause* _conclusion;
  };

public:
  CLASS_NAME(ForwardSubsumptionAndResolution);
  USE_ALLOCATOR(ForwardSubsumptionAndResolution);

  ForwardSubsumptionAndResolution(bool subsumptionResolution=true);
  ~ForwardSubsumptionAndResolution();

  void attach(SaturationAlgorithm* salg) override;
  void detach() override;
  bool perform(Clause* cl, Clause*& replacement, ClauseIterator& premises) override;

  static Clause* generateSubsumptionResolutionClause(Clause* cl, Literal* lit, Clause* baseClause);

  static void printStats(std::ostream& out);

private:
  /** Simplification unit index */
  UnitClauseLiteralIndex* _unitIndex;
  FwSubsSimplifyingLiteralIndex* _fwIndex;

  bool _subsumptionResolution;

  SMTSubsumption::SATSubsumption smtsubs;

  vvector<SubsumptionInstance> subsumption_tried;
  vvector<SubsumptionResolutionInstance> subsumptionResolution_tried;

  bool checkSubsumption(Clause *mcl, ClauseIterator &premises, LiteralMiniIndex &miniIndex);

  Clause* checkSubsumptionResolution(Clause *cl, ClauseIterator &premises, LiteralMiniIndex &miniIndex);
};


};

#endif /* __ForwardSubsumptionAndResolution__ */

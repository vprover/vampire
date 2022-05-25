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

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class ForwardSubsumptionAndResolution
: public ForwardSimplificationEngine
{
public:
  CLASS_NAME(ForwardSubsumptionAndResolution);
  USE_ALLOCATOR(ForwardSubsumptionAndResolution);

  ForwardSubsumptionAndResolution(bool subsumptionResolution=true)
  : _subsumptionResolution(subsumptionResolution) {}

  void attach(SaturationAlgorithm* salg) override;
  void detach() override;
  bool perform(Clause* cl, Clause*& replacement, ClauseIterator& premises) override;

  static Clause* generateSubsumptionResolutionClause(Clause* cl, Literal* lit, Clause* baseClause);
private:
  /** Simplification unit index */
  UnitClauseLiteralIndex* _unitIndex;
  FwSubsSimplifyingLiteralIndex* _fwIndex;

  bool _subsumptionResolution;
};


};

#endif /* __ForwardSubsumptionAndResolution__ */

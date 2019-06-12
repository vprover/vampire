
/*
 * File ForwardSubsumptionAndResolution.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file ForwardSubsumptionAndResolution.hpp
 * Defines class ForwardSubsumptionAndResolution.
 */


#ifndef __ForwardSubsumptionAndResolution__
#define __ForwardSubsumptionAndResolution__


#include "Forwards.hpp"
#include "InferenceEngine.hpp"

#include "Lib/TimeCounter.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class ForwardSubsumptionAndResolutionImplementation {
public:
  ForwardSubsumptionAndResolutionImplementation(bool subsumptionResolution=true) :
    _unitIndex(0), _fwIndex(0), _subsumptionResolution(subsumptionResolution) {}

  void setIndices(UnitClauseLiteralIndex* unitIdx, FwSubsSimplifyingLiteralIndex* fwIdx) {
    _unitIndex = unitIdx;
    _fwIndex = fwIdx;
  }

  void resetIndices() {
    _unitIndex = 0;
    _fwIndex = 0;
  }

  static Clause* generateSubsumptionResolutionClause(Clause* cl, Literal* lit, Clause* baseClause);
  bool genericPerform(Clause* cl, Clause*& replacement, Clause*& thePremise, TimeCounterUnit subTimeCounter, TimeCounterUnit subResTimeCounter);
private:
  /** Simplification unit index */
  UnitClauseLiteralIndex* _unitIndex;
  FwSubsSimplifyingLiteralIndex* _fwIndex;
  bool _subsumptionResolution;
};

class ForwardSubsumptionAndResolution
: public ForwardSimplificationEngine
{
public:
  CLASS_NAME(ForwardSubsumptionAndResolution);
  USE_ALLOCATOR(ForwardSubsumptionAndResolution);

  ForwardSubsumptionAndResolution(bool subsumptionResolution=true)
  : _impl(subsumptionResolution) {}

  void attach(SaturationAlgorithm* salg) override;
  void detach() override;
  bool perform(Clause* cl, Clause*& replacement, ClauseIterator& premises) override;
private:
  ForwardSubsumptionAndResolutionImplementation _impl;
};

};

#endif /* __ForwardSubsumptionAndResolution__ */

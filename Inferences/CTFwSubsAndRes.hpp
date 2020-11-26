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
 * @file CTFwSubsAndRes.hpp
 * Defines class CTFwSubsAndRes.
 */

#ifndef __CTFwSubsAndRes__
#define __CTFwSubsAndRes__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;

class CTFwSubsAndRes
: public ForwardSimplificationEngine
{
public:
  CLASS_NAME(CTFwSubsAndRes);
  USE_ALLOCATOR(CTFwSubsAndRes);

  CTFwSubsAndRes(bool subsumptionResolution)
  : _subsumptionResolution(subsumptionResolution) {}
  
  void attach(SaturationAlgorithm* salg) override;
  void detach() override;
  bool perform(Clause* cl, Clause*& replacement, ClauseIterator& premises) override;
private:
  Clause* buildSResClause(Clause* cl, unsigned resolvedIndex, Clause* premise);

  bool _subsumptionResolution;
  ClauseSubsumptionIndex* _index;
};

}

#endif // __CTFwSubsAndRes__

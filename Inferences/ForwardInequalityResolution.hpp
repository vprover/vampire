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
 * @file ForwardDemodulation.hpp
 * Defines class ForwardDemodulation
 *
 */

#ifndef __ForwardInequalityResolution__
#define __ForwardInequalityResolution__

#include "Forwards.hpp"
#include "Indexing/TermIndex.hpp"

#include "InferenceEngine.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class ForwardInequalityResolution
: public ForwardSimplificationEngine
{
public:
  CLASS_NAME(ForwardInequalityResolution);
  USE_ALLOCATOR(ForwardInequalityResolution);

  void attach(SaturationAlgorithm* salg) override;
  void detach() override;
  bool perform(Clause* cl, Clause*& replacement, ClauseIterator& premises) override;
protected:
  InequalityResolutionUnitIndex* _index;
};


};

#endif /*__ForwardInequalityResolution__*/

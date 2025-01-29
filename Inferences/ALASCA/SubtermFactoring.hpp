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
 * @file SubtermFactoring.hpp
 * Defines class SubtermFactoring
 *
 */

#ifndef __SubtermFactoring__
#define __SubtermFactoring__

#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Kernel/ALASCA.hpp"

namespace Inferences {
namespace ALASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class SubtermFactoring
: public GeneratingInferenceEngine
{
public:
  USE_ALLOCATOR(SubtermFactoring);

  SubtermFactoring(SubtermFactoring&&) = default;
  SubtermFactoring(std::shared_ptr<AlascaState> shared)
    : _shared(std::move(shared))
  {  }

  void attach(SaturationAlgorithm* salg) final override { GeneratingInferenceEngine::attach(salg); }
  void detach() final override { GeneratingInferenceEngine::detach(); }

  ClauseIterator generateClauses(Clause* premise) final override;

#if VDEBUG
  virtual void setTestIndices(Stack<Indexing::Index*> const&) final override {  }
#endif

private:
  std::shared_ptr<AlascaState> _shared;
};

} // namespace ALASCA 
} // namespace Inferences 

#endif /*__SubtermFactoring__*/

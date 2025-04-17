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
 * @file EqFactoring.hpp
 * Defines class EqFactoring
 *
 */

#ifndef __EqFactoring__
#define __EqFactoring__

#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Kernel/ALASCA/SelectionPrimitves.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/ALASCA/Index.hpp"
#include "Shell/Options.hpp"

namespace Inferences {
namespace ALASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class EqFactoring
: public GeneratingInferenceEngine
{
public:
  USE_ALLOCATOR(EqFactoring);

  EqFactoring(EqFactoring&&) = default;
  EqFactoring(std::shared_ptr<AlascaState> shared)
    : _shared(std::move(shared))
  {  }

  void attach(SaturationAlgorithm* salg) final override;
  void detach() final override;

  Option<Clause*> applyRule(SelectedEquality const& e1, SelectedEquality const& e2);
  ClauseIterator generateClauses(Clause* premise) final override;

  // TODO 2
  virtual VirtualIterator<std::tuple<>> lookaheadResultEstimation(__SelectedLiteral const& selection) override
  { return pvi(dropElementType(range(0,1))); }

private:
  std::shared_ptr<AlascaState> _shared;
};

} // namespace ALASCA 
} // namespace Inferences 

#endif /*__EqFactoring__*/

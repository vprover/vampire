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
 * @file VariableElimination.hpp
 * Defines class VariableElimination
 *
 */

#ifndef __Inferences_LASCA_VIRAS__
#define __Inferences_LASCA_VIRAS__

#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Kernel/Ordering.hpp"
#include "Indexing/LascaIndex.hpp"
#include "Shell/Options.hpp"

namespace Inferences {
namespace LASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class VirasQuantifierElimination
: public SimplifyingGeneratingInference
{
public:

  VirasQuantifierElimination(VirasQuantifierElimination&&) = default;
  explicit VirasQuantifierElimination(std::shared_ptr<LascaState> shared) 
    : _shared(std::move(shared))
  {  }

  void attach(SaturationAlgorithm* salg) final override {}
  void detach() final override {}

  ClauseGenerationResult generateSimplify(Clause* premise) final override;


#if VDEBUG
  virtual void setTestIndices(Stack<Indexing::Index*> const&) final override {}
#endif

private:

  std::shared_ptr<LascaState> _shared;
};

} // namespace LASCA 
} // namespace Inferences 

// lalalalala
#endif /*__Inferences_LASCA_VIRAS__*/

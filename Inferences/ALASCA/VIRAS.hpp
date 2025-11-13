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

#ifndef __Inferences_ALASCA_VIRAS__
#define __Inferences_ALASCA_VIRAS__

#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Kernel/ALASCA.hpp"

namespace Inferences {
namespace ALASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class VirasQuantifierElimination
: public SimplifyingGeneratingInference
{
public:

  VirasQuantifierElimination(VirasQuantifierElimination&&) = default;
  explicit VirasQuantifierElimination(std::shared_ptr<AlascaState> shared) 
    : _shared(std::move(shared))
  {  }

  void attach(SaturationAlgorithm* salg) final {}
  void detach() final {}

  ClauseGenerationResult generateSimplify(Clause* premise) final ;

#if VDEBUG
  virtual void setTestIndices(Stack<Indexing::Index*> const&) final override {}
#endif

private:
  Option<ClauseGenerationResult> generateSimplify(IntTraits n, Clause* premise);
  template<class NumTraits>
  Option<ClauseGenerationResult> generateSimplify(NumTraits n, Clause* premise);

  std::shared_ptr<AlascaState> _shared;
};

} // namespace ALASCA 
} // namespace Inferences 

#endif /*__Inferences_ALASCA_VIRAS__*/

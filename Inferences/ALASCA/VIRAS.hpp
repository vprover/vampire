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

#include "Debug/Assertion.hpp"
#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/ALASCA/Index.hpp"
#include "Lib/Exception.hpp"
#include "Shell/Options.hpp"

namespace Inferences {
namespace ALASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class VirasQuantifierElimination
{
  std::shared_ptr<AlascaState> _shared;
public:

  VirasQuantifierElimination(VirasQuantifierElimination&&) = default;
  explicit VirasQuantifierElimination(std::shared_ptr<AlascaState> shared) 
    : _shared(std::move(shared))
  {  }

  Option<VirtualIterator<Clause*>> apply(Clause* premise);
};


class VirasQuantifierEliminationSGI
: public SimplifyingGeneratingInference
{
  VirasQuantifierElimination _self;
public:

  VirasQuantifierEliminationSGI(VirasQuantifierEliminationSGI&&) = default;
  explicit VirasQuantifierEliminationSGI(std::shared_ptr<AlascaState> shared) 
    : _self(std::move(shared))
  {  }

  void attach(SaturationAlgorithm* salg) final override {}
  void detach() final override {}

  ClauseGenerationResult generateSimplify(Clause* premise) final override 
  {
    if (auto res = _self.apply(premise)) {
      return ClauseGenerationResult {
        .clauses = *res,
        .premiseRedundant = true,
      };
    } else {
      return ClauseGenerationResult {
        .clauses = VirtualIterator<Clause*>::getEmpty(),
        .premiseRedundant = false,
      };
    }
  }

  
  /** TODO 2 should we make this a correct estimation */
  virtual VirtualIterator<std::tuple<>> lookaheadResultEstimation(NewSelectedAtom const& selection) override 
  { return pvi(dropElementType(range(0,0))); }

#if VDEBUG
  virtual void setTestIndices(Stack<Indexing::Index*> const&) final override {}
#endif
};

class VirasQuantifierEliminationISE
: public ImmediateSimplificationEngine
{
  VirasQuantifierElimination _self;
public:

  VirasQuantifierEliminationISE(VirasQuantifierEliminationISE&&) = default;
  explicit VirasQuantifierEliminationISE(std::shared_ptr<AlascaState> shared) 
    : _self(std::move(shared))
  {  }

  void attach(SaturationAlgorithm* salg) final override {}
  void detach() final override {}

  // TODO fix class hierarchy so we don't need this ASSERTION_VIOLATION
  Clause* simplify(Clause* premise) final override { ASSERTION_VIOLATION_REP("should only be used with simplifyMany")  }
  ClauseIterator simplifyMany(Clause* premise) final override 
  {
    if (auto result = _self.apply(premise)) {
      if (result->hasNext()) {
        return *result;
      } else {
        return pvi(iterItems<Clause*>(nullptr));
      }
    } else {
      return VirtualIterator<Clause*>::getEmpty();
    }
  }

#if VDEBUG
  virtual void setTestIndices(Stack<Indexing::Index*> const&) final override {}
#endif
};

} // namespace ALASCA 
} // namespace Inferences 

#endif /*__Inferences_ALASCA_VIRAS__*/

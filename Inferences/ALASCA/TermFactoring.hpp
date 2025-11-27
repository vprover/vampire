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
 * @file TermFactoring.hpp
 * Defines class TermFactoring
 *
 */

#ifndef __TermFactoring__
#define __TermFactoring__

#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Kernel/ALASCA.hpp"

namespace Inferences {
namespace ALASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class TermFactoring
: public GeneratingInferenceEngine
{
public:
  USE_ALLOCATOR(TermFactoring);

  TermFactoring(TermFactoring&&) = default;
  TermFactoring(std::shared_ptr<AlascaState> shared)
    : _shared(std::move(shared))
  {  }

  void attach(SaturationAlgorithm* salg) final ;
  void detach() final ;

  ClauseIterator generateClauses(Clause* premise) final ;

#if VDEBUG
  virtual void setTestIndices(Stack<Indexing::Index*> const&) final override {  }
#endif

private:

                            Option<Clause*> applyRule(SelectedSummand const& l, SelectedSummand const& r, Stack<TermList> const& maxAtoms);
  template<class NumTraits> Option<Clause*> applyRule(SelectedSummand const& l, SelectedSummand const& r, Stack<TermList> const& maxAtoms);

  std::shared_ptr<AlascaState> _shared;
};

} // namespace ALASCA 
} // namespace Inferences 

#endif /*__TermFactoring__*/

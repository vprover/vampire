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
#include "Kernel/Ordering.hpp"
#include "Indexing/IndexManager.hpp"
#include "Indexing/TermIndex.hpp"
#include "Inferences/PolynomialEvaluation.hpp"
#include "Kernel/LASCA.hpp"
#include "Shell/Options.hpp"
#include "Debug/Output.hpp"

namespace Inferences {
namespace LASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class TermFactoring
: public GeneratingInferenceEngine
{
public:
  USE_ALLOCATOR(TermFactoring);

  TermFactoring(TermFactoring&&) = default;
  TermFactoring(std::shared_ptr<LascaState> shared)
    : _shared(std::move(shared))
  {  }

  void attach(SaturationAlgorithm* salg) final override;
  void detach() final override;

  ClauseIterator generateClauses(Clause* premise) final override;

#if VDEBUG
  virtual void setTestIndices(Stack<Indexing::Index*> const&) final override;
#endif

private:

                            Option<Clause*> applyRule(SelectedSummand const& l, SelectedSummand const& r, Stack<TermList> const& maxAtoms);
  template<class NumTraits> Option<Clause*> applyRule(SelectedSummand const& l, SelectedSummand const& r, Stack<TermList> const& maxAtoms);

  std::shared_ptr<LascaState> _shared;
};

} // namespace LASCA 
} // namespace Inferences 

#endif /*__TermFactoring__*/

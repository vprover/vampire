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
 * @file FloorTightening.hpp
 * Defines class FloorTightening
 *
 */

#ifndef __FloorTightening__
#define __FloorTightening__

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

class FloorTightening
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(FloorTightening);
  USE_ALLOCATOR(FloorTightening);

  FloorTightening(FloorTightening&&) = default;
  FloorTightening(shared_ptr<LascaState> shared)
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

  InequalityNormalizer const& normalizer() const { return _shared->normalizer; }
  Ordering* ord() const { return _shared->ordering; }
  
  shared_ptr<LascaState> _shared;
};

} // namespace LASCA 
} // namespace Inferences 

#endif /*__FloorTightening__*/

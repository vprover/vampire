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
 * @file InequalityFactoring.hpp
 * Defines class InequalityFactoring
 *
 */

#ifndef __InequalityFactoring__
#define __InequalityFactoring__

#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Kernel/ALASCA/Term.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/ALASCA/Index.hpp"
#include "Shell/Options.hpp"
#include <utility>

namespace Inferences {
namespace ALASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class InequalityFactoring
: public GeneratingInferenceEngine
{
  using SmallArray = SmallArray<Clause*, 2>;
  using Iter = decltype(arrayIter(std::declval<SmallArray>()));
public:
  USE_ALLOCATOR(InequalityFactoring);

  InequalityFactoring(InequalityFactoring&&) = default;
  InequalityFactoring(std::shared_ptr<AlascaState> shared)
    : _shared(std::move(shared))
  {  }

  virtual VirtualIterator<std::tuple<>> lookaheadResultEstimation(SelectedAtom const& selection) override
  { /** if only one atom is selected we will never apply inequality factoring */
    return pvi(dropElementType(range(0, 0))); }

  void attach(SaturationAlgorithm* salg) final override;
  void detach() final override;

  template<class NumTraits>
  Iter generateClauses(Clause* premise, 
    Literal* lit1, AlascaLiteralItp<NumTraits> l1, Monom<NumTraits> j_s1,
    Literal* lit2, AlascaLiteralItp<NumTraits> l2, Monom<NumTraits> k_s2);

  template<class NumTraits>
  Iter applyRule(SelectedAtomicTermItp<NumTraits> const& l1, SelectedAtomicTermItp<NumTraits> const& l2, AbstractingUnifier& uwa);
  Iter applyRule(SelectedAtomicTermItpAny const& l1, SelectedAtomicTermItpAny const& l2, AbstractingUnifier& uwa);

  template<class NumTraits>
  Iter generateClauses(
      Clause* premise,
      Literal* lit1, AlascaLiteralItp<NumTraits> L1,
      Literal* lit2, AlascaLiteralItp<NumTraits> L2
    );

  ClauseIterator generateClauses(Clause* premise) final override;
  

#if VDEBUG
  virtual void setTestIndices(Stack<Indexing::Index*> const&) final override;
#endif

private:

  std::shared_ptr<AlascaState> _shared;
};
#define _alascaFactoring true

} // namespace ALASCA 
} // namespace Inferences 

#endif /*__InequalityFactoring__*/

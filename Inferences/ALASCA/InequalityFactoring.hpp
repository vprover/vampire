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
#include "Kernel/ALASCA.hpp"

namespace Inferences {
namespace ALASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class InequalityFactoring
: public GeneratingInferenceEngine
{
public:
  USE_ALLOCATOR(InequalityFactoring);

  InequalityFactoring(InequalityFactoring&&) = default;
  InequalityFactoring(std::shared_ptr<AlascaState> shared)
    : _shared(std::move(shared))
  {  }

  void attach(SaturationAlgorithm* salg) final ;
  void detach() final ;

  template<class NumTraits>
  ClauseIterator generateClauses(Clause* premise, 
    Literal* lit1, AlascaLiteral<NumTraits> l1, Monom<NumTraits> j_s1,
    Literal* lit2, AlascaLiteral<NumTraits> l2, Monom<NumTraits> k_s2);

  template<class NumTraits>
  Option<Clause*> applyRule(SelectedSummand const& l1, SelectedSummand const& l2);
  Option<Clause*> applyRule(SelectedSummand const& l1, SelectedSummand const& l2);

  template<class NumTraits>
  ClauseIterator generateClauses(
      Clause* premise,
      Literal* lit1, AlascaLiteral<NumTraits> L1,
      Literal* lit2, AlascaLiteral<NumTraits> L2
    );

  ClauseIterator generateClauses(Clause* premise) final ;
  

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

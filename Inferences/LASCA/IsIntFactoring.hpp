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
 * @file IsIntFactoring.hpp
 * Defines class IsIntFactoring
 *
 */

#ifndef __IsIntFactoring__
#define __IsIntFactoring__

#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Indexing/LascaIndex.hpp"
#include "Shell/Options.hpp"

namespace Inferences {
namespace LASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class IsIntFactoring
: public GeneratingInferenceEngine
{
public:
  USE_ALLOCATOR(IsIntFactoring);

  IsIntFactoring(IsIntFactoring&&) = default;
  IsIntFactoring(std::shared_ptr<LascaState> shared)
    : _shared(std::move(shared))
  {  }

  void attach(SaturationAlgorithm* salg) final override;
  void detach() final override;


  template<class NumTraits>
  Stack<Clause*> applyRule(Clause* premise, 
    Literal* lit1, LascaLiteral<NumTraits> l1, Monom<NumTraits> j_s1,
    Literal* lit2, LascaLiteral<NumTraits> l2, Monom<NumTraits> k_s2,
    AbstractingUnifier sigma_cnst);

  template<class NumTraits>
  ClauseIterator generateClauses(Clause* premise, 
    Literal* lit1, LascaLiteral<NumTraits> l1, Monom<NumTraits> j_s1,
    Literal* lit2, LascaLiteral<NumTraits> l2, Monom<NumTraits> k_s2);

  template<class NumTraits>
  Option<Clause*> applyRule(NumTraits, SelectedSummand const& l1, SelectedSummand const& l2);
  Option<Clause*> applyRule(IntTraits, SelectedSummand const& l1, SelectedSummand const& l2) 
  { return Option<Clause*>(); }
  Option<Clause*> applyRule(SelectedSummand const& l1, SelectedSummand const& l2);


  template<class NumTraits>
  ClauseIterator generateClauses(
      Clause* premise,
      Literal* lit1, LascaLiteral<NumTraits> L1,
      Literal* lit2, LascaLiteral<NumTraits> L2
    );

  ClauseIterator generateClauses(Clause* premise) final override;
  

#if VDEBUG
  virtual void setTestIndices(Stack<Indexing::Index*> const&) final override;
#endif

private:

  std::shared_ptr<LascaState> _shared;
};

} // namespace LASCA 
} // namespace Inferences 

#endif /*__IsIntFactoring__*/

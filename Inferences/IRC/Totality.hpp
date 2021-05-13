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
 * @file Totality.hpp
 * Defines class Totality
 *
 */

#ifndef __IRC_Totality__
#define __IRC_Totality__

#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Kernel/Ordering.hpp"
#include "Shell/UnificationWithAbstractionConfig.hpp"
#include "Indexing/InequalityResolutionIndex.hpp"
#include "Shell/Options.hpp"

namespace Inferences {
namespace IRC {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class Totality
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(Totality);
  USE_ALLOCATOR(Totality);

  Totality(Totality&&) = default;
  Totality(shared_ptr<IrcState> shared) 
    : _shared(std::move(shared))
    , _index(nullptr)
  {  }

  void attach(SaturationAlgorithm* salg) final override;
  void detach() final override;


  ClauseIterator generateClauses(Clause* premise) final override;

#if VDEBUG
  virtual void setTestIndices(Stack<Indexing::Index*> const&) final override;
#endif

private:

  template<class NumTraits> Clause* applyRule(
      Clause* hyp1, Literal* lit1, IrcLiteral<NumTraits> l1, Monom<NumTraits> j_s1,
      Clause* hyp2, Literal* lit2, IrcLiteral<NumTraits> l2, Monom<NumTraits> k_s2,
      ResultSubstitution& sigma, Stack<UnificationConstraint>& cnst
      ) const;

  template<class NumTraits> ClauseIterator generateClauses(Clause* clause, Literal* lit, IrcLiteral<NumTraits> l1) const;

  shared_ptr<IrcState> _shared;
  InequalityResolutionIndex* _index;
};

} // namespace IRC 
} // namespace Inferences 

// lalalalala
#endif /*__IRC_Totality__*/

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
 * @file LiteralFactoring.hpp
 * Defines class LiteralFactoring
 *
 */

#ifndef __LiteralFactoring__
#define __LiteralFactoring__

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

template<class A>
struct Indexed {
  unsigned idx;
  A self;
  A& operator*() { return self; }
  A const& operator*() const { return self; }
  A* operator->() { return &self; }
};

template<class A>
Indexed<A> indexed(unsigned idx, A self) 
{ return {.idx = idx, .self = std::move(self), }; }

class LiteralFactoring
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(LiteralFactoring);
  USE_ALLOCATOR(LiteralFactoring);

  LiteralFactoring(LiteralFactoring&&) = default;
  LiteralFactoring(shared_ptr<IrcState> shared) 
    : _shared(std::move(shared))
  {  }

  void attach(SaturationAlgorithm* salg) final override;
  void detach() final override;


  template<class NumTraits>
  Clause* applyRule(Clause* premise, 
    Indexed<IrcLiteral<NumTraits>> l1,  Monom<NumTraits> j_s1,
    Indexed<IrcLiteral<NumTraits>> l2,  Monom<NumTraits> k_s2,
    UwaResult sigma_cnst);
  template<class NumTraits>
  ClauseIterator generateClauses(Clause* premise, Indexed<IrcLiteral<NumTraits>> l1, Indexed<IrcLiteral<NumTraits>> l2);
  ClauseIterator generateClauses(Clause* premise) final override;

  

#if VDEBUG
  virtual void setTestIndices(Stack<Indexing::Index*> const&) final override;
#endif

private:

  shared_ptr<IrcState> _shared;
};

} // namespace IRC 
} // namespace Inferences 

// lalalalala
#endif /*__LiteralFactoring__*/

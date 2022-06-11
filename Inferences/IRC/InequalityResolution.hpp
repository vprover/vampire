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
 * @file InequalityResolution.hpp
 * Defines class InequalityResolution
 *
 */

#ifndef __IRC_InequalityResolution__
#define __IRC_InequalityResolution__

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

class InequalityResolution
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(InequalityResolution);
  USE_ALLOCATOR(InequalityResolution);

  InequalityResolution(InequalityResolution&&) = default;
  InequalityResolution(shared_ptr<IrcState> shared) 
    : _shared(std::move(shared))
    , _lhsIndex()
    , _rhsIndex()
  {  }

  class Lhs : public SelectedSummand { 
  public: 
    explicit Lhs(Lhs const&) = default;
    Lhs(SelectedSummand s) : SelectedSummand(std::move(s)) {} 
    Lhs(Lhs&&) = default;
    Lhs& operator=(Lhs&&) = default;

    static auto iter(IrcState& shared, Clause* cl)
    { return shared.selectedSummands(cl, /* literal*/ SelectionCriterion::STRICTLY_MAX, /* term */ SelectionCriterion::STRICTLY_MAX)
              .filter([&](auto const& selected) { return selected.isInequality(); })
              .filter([&](auto const& selected) { return selected.sign()   == Sign::Pos; })
              .map([&]   (auto selected)        { return Lhs(std::move(selected));     }); }
  };

  class Rhs : public SelectedSummand { 
  public: 

    explicit Rhs(Rhs const&) = default;
    Rhs(SelectedSummand s) : SelectedSummand(std::move(s)) {} 
    Rhs(Rhs&&) = default;
    Rhs& operator=(Rhs&&) = default;

    static auto iter(IrcState& shared, Clause* cl) 
    { return shared.selectedSummands(cl, /* literal*/ SelectionCriterion::STRICTLY_MAX, /* term */ SelectionCriterion::WEAKLY_MAX)
              .filter([&](auto const& selected) { return selected.isInequality(); })
              .filter([&](auto const& selected) { return selected.sign() == Sign::Neg; })
              .map([&]   (auto selected)        { return Rhs(std::move(selected));     }); }
  };

  void attach(SaturationAlgorithm* salg) final override;
  void detach() final override;

  ClauseIterator generateClauses(Clause* premise) final override;

#if VDEBUG
  virtual void setTestIndices(Stack<Indexing::Index*> const&) final override;
#endif
    
private:
  Option<Clause*> applyRule(
      Lhs const& lhs, unsigned lhsVarBank,
      Rhs const& rhs, unsigned rhsVarBank,
      UwaResult& uwa
      ) const;

  template<class NumTraits, class Subst, class CnstIter> Option<Clause*> applyRule(
      Clause* hyp1, Literal* lit1, IrcLiteral<NumTraits> l1, Monom<NumTraits> j_s1,
      Clause* hyp2, Literal* lit2, IrcLiteral<NumTraits> l2, Monom<NumTraits> k_s2,
      Subst sigma, CnstIter cnst, unsigned nCnst
      ) const;

  template<class NumTraits> ClauseIterator generateClauses(Clause* clause, Literal* lit, IrcLiteral<NumTraits> l1, Monom<NumTraits> j_s1) const;

  shared_ptr<IrcState> _shared;
  IrcIndex<Lhs>* _lhsIndex;
  IrcIndex<Rhs>* _rhsIndex;
};

} // namespace IRC 
} // namespace Inferences 


#endif /*__IRC_InequalityResolution__*/

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
 * @file FourierMotzkin.hpp
 * Defines class FourierMotzkin
 *
 */

#ifndef __LASCA_FourierMotzkin__
#define __LASCA_FourierMotzkin__

#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Kernel/Ordering.hpp"
#include "Shell/UnificationWithAbstractionConfig.hpp"
#include "Indexing/LascaIndex.hpp"
#include "Shell/Options.hpp"

namespace Inferences {
namespace LASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class FourierMotzkin
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(FourierMotzkin);
  USE_ALLOCATOR(FourierMotzkin);

  FourierMotzkin(FourierMotzkin&&) = default;
  FourierMotzkin(shared_ptr<LascaState> shared) 
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

    static auto iter(LascaState& shared, Clause* cl)
    { 
      CALL("Lasca::FourierMotzkin::Lhs::iter")
      return shared.selectedSummands(cl, 
                        /* literal*/ SelectionCriterion::STRICTLY_MAX, 
                        /* term */ SelectionCriterion::STRICTLY_MAX,
                        /* include number vars */ false)
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

    static auto iter(LascaState& shared, Clause* cl) 
    { 
      CALL("Lasca::FourierMotzkin::Rhs::iter")
      return shared.selectedSummands(cl, 
                        /* literal*/ SelectionCriterion::STRICTLY_MAX,
                        /* term */ SelectionCriterion::WEAKLY_MAX,
                        /* include number vars */ false)
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

  template<class NumTraits> ClauseIterator generateClauses(Clause* clause, Literal* lit, LascaLiteral<NumTraits> l1, Monom<NumTraits> j_s1) const;

  shared_ptr<LascaState> _shared;
  LascaIndex<Lhs>* _lhsIndex;
  LascaIndex<Rhs>* _rhsIndex;
};

} // namespace LASCA 
} // namespace Inferences 


#endif /*__LASCA_FourierMotzkin__*/

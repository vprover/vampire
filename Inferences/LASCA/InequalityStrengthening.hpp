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
 * @file InequalityStrengthening.hpp
 * Defines class InequalityStrengthening
 *
 */

#ifndef __LASCA_InequalityStrengthening__
#define __LASCA_InequalityStrengthening__

#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Kernel/LASCA.hpp"
#include "Kernel/Ordering.hpp"
#include "Indexing/LascaIndex.hpp"
#include "Shell/Options.hpp"
#include "FourierMotzkin.hpp"
#include "IsIntResolution.hpp"

namespace Inferences {
namespace LASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class InequalityStrengthening
: public GeneratingInferenceEngine
{
public:
  USE_ALLOCATOR(InequalityStrengthening);

  InequalityStrengthening(InequalityStrengthening&&) = default;
  InequalityStrengthening(std::shared_ptr<LascaState> shared) 
    : _shared(std::move(shared))
    , _lhsIndex()
    , _rhsIndex()
  {  }

  using Lhs = IsIntResolution::Lhs;
  class Rhs : public SelectedSummand { 
  public: 
    static const char* name() { return "lasca inequality strengthening rhs"; }

    explicit Rhs(Rhs const&) = default;
    Rhs(SelectedSummand s) : SelectedSummand(std::move(s)) {} 
    Rhs(Rhs&&) = default;
    Rhs& operator=(Rhs&&) = default;

    static auto iter(LascaState& shared, Clause* cl) 
    { return shared.selectedSummands(cl, 
                        /* literal*/ SelectionCriterion::NOT_LESS,
                        /* term */ SelectionCriterion::NOT_LEQ,
                        /* include number vars */ false)
              .filter([&](auto const& selected) { return selected.symbol() == LascaPredicate::GREATER; })
              .filter([&](auto const& selected) { return selected.sign() != Sign::Zero; })
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
      AbstractingUnifier& uwa
      ) const;


  Option<Clause*> applyRule(IntTraits,
      Lhs const& lhs, unsigned lhsVarBank,
      Rhs const& rhs, unsigned rhsVarBank,
      AbstractingUnifier& uwa
      ) const { ASSERTION_VIOLATION }


  template<class NumTraits>
  Option<Clause*> applyRule(NumTraits,
      Lhs const& lhs, unsigned lhsVarBank,
      Rhs const& rhs, unsigned rhsVarBank,
      AbstractingUnifier& uwa
      ) const;

  template<class NumTraits> ClauseIterator generateClauses(Clause* clause, Literal* lit, LascaLiteral<NumTraits> l1, Monom<NumTraits> j_s1) const;

  std::shared_ptr<LascaState> _shared;
  LascaIndex<Lhs>* _lhsIndex;
  LascaIndex<Rhs>* _rhsIndex;
};

} // namespace LASCA 
} // namespace Inferences 


#endif /*__LASCA_InequalityStrengthening__*/

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

#include "Indexing/IndexManager.hpp"
#include "Inferences/InferenceEngine.hpp"
#include "Kernel/Ordering.hpp"
#include "Indexing/LascaIndex.hpp"
#include "BinInf.hpp"
#include "Shell/Options.hpp"

namespace Inferences {
namespace LASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

struct FourierMotzkinConf
{
  FourierMotzkinConf(std::shared_ptr<LascaState> shared) 
    : _shared(std::move(shared))
  {  }

  class Lhs : public SelectedSummand { 
  public: 
    static const char* name() { return "lasca fourier motzkin lhs"; }
    static IndexType indexType() { return Indexing::LASCA_FOURIER_MOTZKIN_LHS_SUBST_TREE; }

    explicit Lhs(Lhs const&) = default;
    Lhs(SelectedSummand s) : SelectedSummand(std::move(s)) {} 
    Lhs(Lhs&&) = default;
    Lhs& operator=(Lhs&&) = default;

    static auto iter(LascaState& shared, Clause* cl)
    { 
      return shared.selectedSummands(cl, 
                        /* literal*/ SelectionCriterion::NOT_LEQ, 
                        /* term */ SelectionCriterion::NOT_LEQ,
                        /* include number vars */ false)
              .filter([&](auto const& selected) { return selected.isInequality(); })
              .filter([&](auto const& selected) { return selected.sign()   == Sign::Pos; })
              .map([&]   (auto selected)        { return Lhs(std::move(selected));     }); }
  };

  class Rhs : public SelectedSummand { 
  public: 
    static const char* name() { return "lasca fourier motzkin rhs"; }
    static IndexType indexType() { return Indexing::LASCA_FOURIER_MOTZKIN_RHS_SUBST_TREE; }

    explicit Rhs(Rhs const&) = default;
    Rhs(SelectedSummand s) : SelectedSummand(std::move(s)) {} 
    Rhs(Rhs&&) = default;
    Rhs& operator=(Rhs&&) = default;

    static auto iter(LascaState& shared, Clause* cl) 
    { 
      return shared.selectedSummands(cl, 
                        /* literal*/ SelectionCriterion::NOT_LESS,
                        /* term */ SelectionCriterion::NOT_LEQ,
                        /* include number vars */ false)
              .filter([&](auto const& selected) { return selected.isInequality(); })
              .filter([&](auto const& selected) { return selected.sign() == Sign::Neg; })
              .map([&]   (auto selected)        { return Rhs(std::move(selected));     }); }
  };

  auto applyRule(
      Lhs const& lhs, unsigned lhsVarBank,
      Rhs const& rhs, unsigned rhsVarBank,
      AbstractingUnifier& uwa
      ) const 
  { return applyRule_(lhs,lhsVarBank, rhs, rhsVarBank, uwa).intoIter(); }

  Option<Clause*> applyRule_(
      Lhs const& lhs, unsigned lhsVarBank,
      Rhs const& rhs, unsigned rhsVarBank,
      AbstractingUnifier& uwa
      ) const;

  std::shared_ptr<LascaState> _shared;
};

struct FourierMotzkin : public BinInf<FourierMotzkinConf>  {
  FourierMotzkin(std::shared_ptr<LascaState> state) 
    : BinInf<FourierMotzkinConf>(state, FourierMotzkinConf(state)) {}
};

} // namespace LASCA 
} // namespace Inferences 


#endif /*__LASCA_FourierMotzkin__*/

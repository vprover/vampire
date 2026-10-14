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

#ifndef __ALASCA_Inferences_FourierMotzkin__
#define __ALASCA_Inferences_FourierMotzkin__

#include "Forwards.hpp"

#include "BinInf.hpp"

namespace Inferences {
namespace ALASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

struct FourierMotzkinConf
{
  FourierMotzkinConf(SaturationAlgorithm& salg) 
    : _shared(salg.alascaState())
  {  }

  static const char* name() { return "alasca fourier motzkin"; }

  class Lhs : public SelectedSummand { 
  public: 
    static const char* name() { return "alasca fourier motzkin lhs"; }

    explicit Lhs(Lhs const&) = default;
    Lhs(SelectedSummand s) : SelectedSummand(std::move(s)) {} 
    Lhs(Lhs&&) = default;
    Lhs& operator=(Lhs&&) = default;

    static auto iter(AlascaState& shared, Clause* cl)
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
    static const char* name() { return "alasca fourier motzkin rhs"; }

    explicit Rhs(Rhs const&) = default;
    Rhs(SelectedSummand s) : SelectedSummand(std::move(s)) {} 
    Rhs(Rhs&&) = default;
    Rhs& operator=(Rhs&&) = default;

    static auto iter(AlascaState& shared, Clause* cl) 
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

  AlascaState& _shared;
};

struct FourierMotzkin : public BinInf<FourierMotzkinConf>  {
  FourierMotzkin(SaturationAlgorithm& salg) 
    : BinInf<FourierMotzkinConf>(salg, FourierMotzkinConf(salg)) {}
};

} // namespace ALASCA 
} // namespace Inferences 


#endif /*__ALASCA_Inferences_FourierMotzkin__*/

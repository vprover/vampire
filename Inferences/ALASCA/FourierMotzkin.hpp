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

#include "Indexing/IndexManager.hpp"
#include "Inferences/InferenceEngine.hpp"
#include "Kernel/ALASCA/Ordering.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/ALASCA/Index.hpp"
#include "BinInf.hpp"
#include "Shell/Options.hpp"

namespace Inferences {
namespace ALASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

struct FourierMotzkinConf
{
  FourierMotzkinConf(std::shared_ptr<AlascaState> shared) 
    : _shared(std::move(shared))
  {  }

  static const char* name() { return "alasca fourier motzkin"; }

  class Lhs : public SelectedAtomicTermItpAny { 
  public: 
    static const char* name() { return "alasca fourier motzkin lhs"; }
    static IndexType indexType() { return Indexing::ALASCA_FOURIER_MOTZKIN_LHS_SUBST_TREE; }

    explicit Lhs(Lhs const&) = default;
    Lhs(SelectedAtomicTermItpAny s) : SelectedAtomicTermItpAny(std::move(s)) {} 
    Lhs(Lhs&&) = default;
    Lhs& operator=(Lhs&&) = default;
    
    TypedTermList key() const { return selectedAtomicTerm(); }

    static auto iter(AlascaState& shared, __SelectedLiteral const& sel) {
      return SelectedAtomicTermItpAny::iter(shared.ordering, sel, literalMaximality(), atomMaximality())
              .filter([&](auto const& selected) { return selected.isInequality(); })
              .filter([&](auto const& selected) { return selected.sign()   == Sign::Pos; })
              .map([&]   (auto selected)        { return Lhs(std::move(selected));     });
    }

    static SelectionCriterion literalMaximality() { return SelectionCriterion::NOT_LEQ; }
    static SelectionCriterion    atomMaximality() { return SelectionCriterion::NOT_LEQ; }

    static auto iter(AlascaState& shared, Clause* cl)
    { 
      return shared.selected(cl, /* literal*/ SelectionCriterion::NOT_LEQ, 
                                 /* term */ SelectionCriterion::NOT_LEQ,
                                 /* include number vars */ false)
              .flatMap([&shared](auto selected) { return iter(shared, selected); }); }

  };

  class Rhs : public SelectedAtomicTermItpAny { 
  public: 
    static const char* name() { return "alasca fourier motzkin rhs"; }
    static IndexType indexType() { return Indexing::ALASCA_FOURIER_MOTZKIN_RHS_SUBST_TREE; }

    explicit Rhs(Rhs const&) = default;
    Rhs(SelectedAtomicTermItpAny s) : SelectedAtomicTermItpAny(std::move(s)) {} 
    Rhs(Rhs&&) = default;
    Rhs& operator=(Rhs&&) = default;

    TypedTermList key() const { return selectedAtomicTerm(); }

    static auto iter(AlascaState& shared, __SelectedLiteral const& sel) {
      return SelectedAtomicTermItpAny::iter(shared.ordering, sel, literalMaximality(), atomMaximality())
              .filter([&](auto const& selected) { return selected.isInequality(); })
              .filter([&](auto const& selected) { return selected.sign() == Sign::Neg; })
              .map([&]   (auto selected)        { return Rhs(std::move(selected));     });
    }

    static SelectionCriterion literalMaximality() { return SelectionCriterion::NOT_LESS; }
    static SelectionCriterion    atomMaximality() { return SelectionCriterion::NOT_LEQ; }

    static auto iter(AlascaState& shared, Clause* cl) 
    { 
      return shared.selected(cl, /* literal*/ SelectionCriterion::NOT_LESS,
                                 /* term */ SelectionCriterion::NOT_LEQ,
                                 /* include number vars */ false)
              .flatMap([&shared](auto selected) { return iter(shared, selected); });
    }
              
  };

  auto applyRule(
      Lhs const& lhs, unsigned lhsVarBank,
      Rhs const& rhs, unsigned rhsVarBank,
      AbstractingUnifier& uwa
      ) const 
  { return iterItems(applyRule_(lhs,lhsVarBank, rhs, rhsVarBank, uwa)); }

  Clause* applyRule_(
      Lhs const& lhs, unsigned lhsVarBank,
      Rhs const& rhs, unsigned rhsVarBank,
      AbstractingUnifier& uwa
      ) const;

  std::shared_ptr<AlascaState> _shared;
};

struct FourierMotzkin : public BinInf<FourierMotzkinConf>  {
  FourierMotzkin(std::shared_ptr<AlascaState> state) 
    : BinInf<FourierMotzkinConf>(state, FourierMotzkinConf(state)) {}
};

} // namespace ALASCA 
} // namespace Inferences 


#endif /*__ALASCA_Inferences_FourierMotzkin__*/

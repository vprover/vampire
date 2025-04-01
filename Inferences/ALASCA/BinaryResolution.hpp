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
 * @file BinaryResolution.hpp
 * Defines class BinaryResolution
 *
 */

#ifndef __ALASCA_Inferences_BinaryResolution__
#define __ALASCA_Inferences_BinaryResolution__

#include "Forwards.hpp"

#include "Indexing/IndexManager.hpp"
#include "Indexing/SubstitutionTree.hpp"
#include "Inferences/InferenceEngine.hpp"
#include "Kernel/ALASCA/SelectionPrimitves.hpp"
#include "Kernel/NumTraits.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/ALASCA/Index.hpp"
#include "Inferences/BinaryResolution.hpp"
#include "BinInf.hpp"
#include "Saturation/SaturationAlgorithm.hpp"
#include "Shell/Options.hpp"

#define DEBUG(...) // DBG(__VA_ARGS__)

namespace Inferences {
namespace ALASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;


struct BinaryResolutionConf
{
  std::shared_ptr<AlascaState> _shared;

  static const char* name() { return "alasca binary resolution"; }

  BinaryResolutionConf(std::shared_ptr<AlascaState> shared) : _shared(shared) {  }

  struct Lhs : public SelectedAtomicLiteral
  {
    static const char* name() { return "alasca binary resolution lhs"; }

    Lhs(SelectedAtomicLiteral inner) : SelectedAtomicLiteral(std::move(inner)) {}

    Literal* key() const { return literal(); }

    static auto iter(AlascaState& shared, SelectedAtom const& sel) {
      return iterTraits(sel.as<SelectedAtomicLiteral>()
             .filter([](auto x) { return x.literal()->isPositive(); })
             .map([](auto x) { return Lhs(std::move(x)); })
             .intoIter());
    }
    
    static SelectionCriterion    atomMaximality() { return SelectionCriterion::NOT_LEQ; }
    static SelectionCriterion literalMaximality() { return /* same as atom maximality for uninterpreted predicates */ SelectionCriterion::ANY; }

    static auto iter(AlascaState& shared, Clause* cl)
    {
      // TODO 3 sort out selection criterions
      return shared.selected(cl, /* literal */ SelectionCriterion::NOT_LEQ, /* selTerm */ SelectionCriterion::ANY, /*includeUnshieldedNumberVariables=*/ false)
               .flatMap([&shared](auto selected) { return iter(shared, selected); });
    }

    static IndexType indexType() { return Indexing::ALASCA_BINARY_RESOLUTION_LHS_SUBST_TREE; }
  };


  struct Rhs : public SelectedAtomicLiteral
  {
    static const char* name() { return "alasca binary resolution rhs"; }

    Rhs(SelectedAtomicLiteral inner) : SelectedAtomicLiteral(std::move(inner)) {}

    Literal* key() const { return Literal::positiveLiteral(literal()); }

    static auto iter(AlascaState& shared, SelectedAtom const& sel) {
      return iterTraits(sel.as<SelectedAtomicLiteral>()
             .filter([](auto x) { return !x.literal()->isPositive(); })
             .map([](auto x) { return Rhs(std::move(x)); })
             .intoIter());
    }

    static SelectionCriterion    atomMaximality() { return SelectionCriterion::NOT_LESS; }
    static SelectionCriterion literalMaximality() { return /* same as atom maximality for uninterpreted predicates */ SelectionCriterion::ANY; }

    static auto iter(AlascaState& shared, Clause* cl)
    {
      // TODO 3 sort out selection criterions
      return shared.selected(cl, /* literal */ SelectionCriterion::NOT_LESS, /* selTerm */ SelectionCriterion::ANY, /*includeUnshieldedNumberVariables=*/ false)
               .flatMap([&shared](auto selected) { return iter(shared, selected); });
    }

    static IndexType indexType() { return Indexing::ALASCA_BINARY_RESOLUTION_RHS_SUBST_TREE; }
  };

  auto applyRule(
      Lhs const& lhs, unsigned lhsVarBank,
      Rhs const& rhs, unsigned rhsVarBank,
      AbstractingUnifier& uwa
      ) const 
  { return applyRule_(&lhs, lhsVarBank, &rhs, rhsVarBank, uwa).intoIter(); }

  Option<Clause*> applyRule_(
      SelectedAtomicLiteral const* lhs, unsigned lhsVarBank,
      SelectedAtomicLiteral const* rhs, unsigned rhsVarBank,
      AbstractingUnifier& uwa
      ) const {
    if (lhsVarBank != subsTreeQueryBank(0)) {
      ASS_EQ(rhsVarBank, subsTreeQueryBank(0))
      std::swap(lhs, rhs);
      std::swap(lhsVarBank, rhsVarBank);
    }
    ASS(_salg)
    auto res = Inferences::BinaryResolution::generateClause(
        lhs->clause(), lhs->literal(), 
        rhs->clause(), rhs->literal(),
        uwa, *env.options, _salg);
    return res == nullptr ? Option<Clause*>() : some(res);
  }
  // TODO somehow get rid of this field and the hack around it
  SaturationAlgorithm* _salg = 0;
  friend void attachToInner(BinaryResolutionIndex& self, SaturationAlgorithm* salg);
};

inline void attachToInner(BinaryResolutionConf& self, SaturationAlgorithm* salg)  {
  self._salg = salg;
}

struct BinaryResolution 
: public BinInf<BinaryResolutionConf> 
{
  BinaryResolution(std::shared_ptr<AlascaState> shared) : BinInf<BinaryResolutionConf>(shared, BinaryResolutionConf(shared)) {}
};


#undef DEBUG
} // namespaceALASCA 
} // namespace Inferences

#endif /*__ALASCA_Inferences_BinaryResolution__*/

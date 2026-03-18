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

#include "Indexing/SubstitutionTree.hpp"
#include "Inferences/BinaryResolution.hpp"
#include "BinInf.hpp"
#include "Saturation/SaturationAlgorithm.hpp"

#define DEBUG(...) // DBG(__VA_ARGS__)

namespace Inferences {
namespace ALASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;


struct BinaryResolutionConf
{
  static const char* name() { return "alasca binary resolution"; }

  BinaryResolutionConf(SaturationAlgorithm& salg) : _salg(salg) {  }

  struct Lhs : public SelectedLiteral
  {
    static const char* name() { return "alasca binary resolution lhs"; }

    Lhs(SelectedLiteral inner) : SelectedLiteral(std::move(inner)) {}

    Literal* key() const { return literal(); }

    static auto iter(AlascaState& shared, Clause* cl)
    {
      return shared.selectedUninterpretedLiterals(cl, /* literal */ SelectionCriterion::NOT_LEQ)
             .filter([](auto x) { return x.literal()->isPositive(); })
             .map([](auto x) { return Lhs(std::move(x)); });
    }
  };


  struct Rhs : public SelectedLiteral
  {
    static const char* name() { return "alasca binary resolution rhs"; }

    Rhs(SelectedLiteral inner) : SelectedLiteral(std::move(inner)) {}

    Literal* key() const { return Literal::positiveLiteral(literal()); }

    static auto iter(AlascaState& shared, Clause* cl)
    {
      return shared.selectedUninterpretedLiterals(cl, /* literal */ SelectionCriterion::NOT_LESS)
             .filter([](auto x) { return !x.literal()->isPositive(); })
             .map([](auto x) { return Rhs(std::move(x)); });
    }
  };

  auto applyRule(
      Lhs const& lhs, unsigned lhsVarBank,
      Rhs const& rhs, unsigned rhsVarBank,
      AbstractingUnifier& uwa
      ) const 
  { return applyRule_(&lhs, lhsVarBank, &rhs, rhsVarBank, uwa).intoIter(); }

  Option<Clause*> applyRule_(
      SelectedLiteral const* lhs, unsigned lhsVarBank,
      SelectedLiteral const* rhs, unsigned rhsVarBank,
      AbstractingUnifier& uwa
      ) const {
    if (lhsVarBank != subsTreeQueryBank(0)) {
      ASS_EQ(rhsVarBank, subsTreeQueryBank(0))
      std::swap(lhs, rhs);
      std::swap(lhsVarBank, rhsVarBank);
    }
    auto res = Inferences::BinaryResolution::generateClause(
        lhs->clause(), lhs->literal(), 
        rhs->clause(), rhs->literal(),
        uwa, _salg.getOptions(), _salg);
    return res == nullptr ? Option<Clause*>() : some(res);
  }
  // TODO somehow get rid of this field and the hack around it
  SaturationAlgorithm& _salg;
};

struct BinaryResolution 
: public BinInf<BinaryResolutionConf> 
{
  BinaryResolution(SaturationAlgorithm& salg) : BinInf<BinaryResolutionConf>(salg, BinaryResolutionConf(salg)) {}
};


#undef DEBUG
} // namespaceALASCA 
} // namespace Inferences

#endif /*__ALASCA_Inferences_BinaryResolution__*/

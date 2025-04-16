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
 * @file Superposition.cpp
 * Defines class Superposition
 *
 */

#include "Superposition.hpp"
#include "Indexing/SubstitutionTree.hpp"
#include "Lib/Metaiterators.hpp"
#include "Saturation/SaturationAlgorithm.hpp"
#include "Shell/Statistics.hpp"
#include "Debug/TimeProfiling.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/OrderingUtils.hpp"
#include "Kernel/ALASCA.hpp"

#define DEBUG(lvl, ...) if (lvl < 0) DBG(__VA_ARGS__)

namespace Inferences {
namespace ALASCA {

// C1 \/ s1 ≈ t             C2 \/ L[s2]
// ====================================
//   (C1 \/ C2 \/ L[t])σ \/ Cnst
// where
// • uwa(s1,s2)=⟨σ,Cnst⟩
// • (s1 ≈ t)σ /⪯ C1σ
// •    L[s2]σ  ∈ Lit+ and L[s2]σ /⪯ C2σ
//   or L[s2]σ /∈ Lit+ and L[s2]σ /≺ C2σ
// • s2σ ⊴ x ∈ active(L[s2]σ)
// • s1σ /⪯ tσ
// • s1 is not a variable
// • s2 is not a variable
//
// • L[s2]σ /⪯ (s1 ≈ t) σ
Option<Clause*> SuperpositionConf::applyRule_(
    Lhs const& lhs, unsigned lhsVarBank,
    Rhs const& rhs, unsigned rhsVarBank,
    AbstractingUnifier& uwa
    ) const 
{
  TIME_TRACE("alasca superposition application")
  DEBUG(1, "lhs: ", lhs);
  DEBUG(1, "rhs: ", rhs);

  ASS (lhs.literal()->isEquality() && lhs.literal()->isPositive())
  auto s2 = TermList(rhs.toRewrite().toTerm());
  auto nothing = [&]() { return Option<Clause*>(); };
  ASS_REP(!s2.isVar(), rhs)

  auto sigma = [&](auto t, auto bank) { return uwa.subs().apply(t, bank); };

#define check_side_condition(cond, cond_code)                                             \
    if (!(cond_code)) {                                                                   \
      DEBUG(2, "side condition not fulfiled: ", cond)                                     \
      return nothing();                                                                   \
    }                                                                                     \

  auto unifySorts = [](auto s1, auto s2) -> Option<TermList> {
    static RobSubstitution subst;
    if (!subst.unify(s1, 0, s2, 0)) {
      return Option<TermList>();
    } else {
      ASS_EQ(subst.apply(s1,0), subst.apply(s2,0))
      return Option<TermList>(subst.apply(s1, 0));
    }
  };

  auto sort = unifySorts(
        SortHelper::getEqualityArgumentSort(lhs.literal()), 
        SortHelper::getResultSort(s2.term())
      );

  check_side_condition(
      "s1 and s2 are of unifyable sorts", 
      sort.isSome())

  auto s2σ = sigma(s2, rhsVarBank);
  auto tσ  = sigma(lhs.smallerSide(), lhsVarBank);
  auto L2σ = sigma(rhs.literal(), rhsVarBank);

  auto resolvent = EqHelper::replace(L2σ, s2σ, tσ);
  //   ^^^^^^^^^--> L[t]σ
  DEBUG(3, "replacing: ", *L2σ, " [ ", s2σ, " -> ", tσ, " ] ==> ", *resolvent);

  Inference inf(GeneratingInference2(Kernel::InferenceRule::ALASCA_SUPERPOSITION, lhs.clause(), rhs.clause()));
  auto out = Clause::fromIterator(concatIters(
          lhs.contextLiterals().map([&](auto l) { return sigma(l, lhsVarBank); }),
          rhs.contextLiterals().map([&](auto l) { 
            auto Lσ = sigma(l, rhsVarBank); 
            return _simultaneousSuperposition ? EqHelper::replace(Lσ, s2σ, tσ) : Lσ;
          }),
          arrayIter(uwa.computeConstraintLiterals()),
          iterItems(resolvent)
        ), inf);
  DEBUG(1, "out: ", *out);
  return Option<Clause*>(out);
}

} // namespace ALASCA 
} // namespace Inferences 

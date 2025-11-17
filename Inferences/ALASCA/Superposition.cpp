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
#include "Lib/Metaiterators.hpp"
#include "Debug/TimeProfiling.hpp"
#include "Kernel/EqHelper.hpp"

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
Option<Clause*> SuperpositionConf::applyRule_(
    Lhs const& lhs, unsigned lhsVarBank,
    Rhs const& rhs, unsigned rhsVarBank,
    AbstractingUnifier& uwa
    ) const 
{
  TIME_TRACE("alasca superposition application")

  ASS (lhs.literal()->isEquality() && lhs.literal()->isPositive())
#if VDEBUG
  auto s1 = lhs.biggerSide();
#endif
  auto s2 = rhs.toRewrite();
  auto nothing = [&]() { return Option<Clause*>(); };
  ASS(!(s1.isVar() && lhs.isFracNum()))
  ASS(!s2.isVar())

  auto cnst = uwa.computeConstraintLiterals();
  auto sigma = [&](auto t, auto bank) { return uwa.subs().apply(t, bank); };

#define check_side_condition(cond, cond_code)                                             \
    if (!(cond_code)) {                                                                   \
      DEBUG(2, "side condition not fulfilled: ", cond)                                    \
      return nothing();                                                                   \
    }                                                                                     \



  Stack<Literal*> concl(lhs.clause()->size() - 1 // <- C1σ
                      + rhs.clause()->size() - 1 // <- C2σ
                      + 1                        // <- L[s2]σ 
                      + cnst->size());      // <- Cnstσ


  auto unifySorts = [](auto s1, auto s2) -> Option<TermList> {
    static RobSubstitution subst;
    if (!subst.unify(s1, 0, s2, 0)) {
      return Option<TermList>();
    } else {
      ASS_EQ(subst.apply(s1,0), subst.apply(s2,0))
      return Option<TermList>(subst.apply(s1, 0));
    }
  };

  check_side_condition(
      "s1 and s2 are of unifyable sorts", 
      unifySorts(
        SortHelper::getEqualityArgumentSort(lhs.literal()), 
        SortHelper::getResultSort(s2.term())
        ).isSome()
      )

  auto L1σ = sigma(lhs.literal(), lhsVarBank);
  check_side_condition(
        "(s1 ≈ t)σ /⪯ C1σ",
        lhs.contextLiterals()
           .all([&](auto L) {
             auto Lσ = sigma(L, lhsVarBank);
             concl.push(Lσ);
             return _shared->notLeq(L1σ, Lσ);
           }))

  auto s2σ = sigma(s2, rhsVarBank);
  auto tσ  = sigma(lhs.smallerSide(), lhsVarBank);

  // •    L[s2]σ  ∈ Lit+ and L[s2]σ /⪯ C2σ
  //   or L[s2]σ /∈ Lit+ and L[s2]σ /≺ C2σ
  auto L2σ = sigma(rhs.literal(), rhsVarBank);
  bool inLitPlus = rhs.inLitPlus();
  check_side_condition(
      inLitPlus ? "L[s2]σ /⪯ C2σ"
                : "L[s2]σ /≺ C2σ",
        rhs.contextLiterals()
           .all([&](auto L) {
             auto Lσ = sigma(L, rhsVarBank);
             if (_simultaneousSuperposition) {
               concl.push(EqHelper::replace(Lσ, s2σ, tσ));
             } else {
               concl.push(Lσ);
             }
             return inLitPlus ? _shared->notLeq(L2σ, Lσ)
                              : _shared->notLess(L2σ, Lσ);
           }));

  check_side_condition(
      "s2σ ⊴ ti ∈ active(L[s2]σ)", 
      _shared->activePositions(L2σ)
        .any([&](auto ti) 
             { return _shared->subtermEqModT(s2σ, ti); }))

  check_side_condition(
      "L[s2]σ /⪯ L1σ", // TODO is this the correct thing? if so make sure we do that for fourrier motzkin and friends as well
      _shared->notLeq(L2σ, L1σ))


  auto s1σ = sigma(lhs.biggerSide() , lhsVarBank);
  check_side_condition(
      "s1σ /⪯ tσ",
      _shared->notLeq(s1σ.untyped(), tσ))


  auto resolvent = EqHelper::replace(L2σ, s2σ, tσ);
  //   ^^^^^^^^^--> L[t]σ
  DEBUG(3, "replacing: ", *L2σ, " [ ", s2σ, " -> ", tσ, " ] ==> ", *resolvent);
  concl.push(resolvent);

  // adding Cnst
  concl.loadFromIterator(cnst->iterFifo());

  Inference inf(GeneratingInference2(Kernel::InferenceRule::ALASCA_SUPERPOSITION, lhs.clause(), rhs.clause()));
  auto out = Clause::fromStack(concl, inf);
  DEBUG(1, "out: ", *out);
  return Option<Clause*>(out);
}

} // namespace ALASCA 
} // namespace Inferences 

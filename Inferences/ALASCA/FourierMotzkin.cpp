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
 * @file FourierMotzkin.cpp
 * Implements class FourierMotzkin.
 */

#include "FourierMotzkin.hpp"
#include "Debug/TimeProfiling.hpp"

#define DEBUG_FM(lvl, ...) if (lvl <= 0) DBG(__VA_ARGS__)

namespace Inferences {
namespace ALASCA {


Option<Clause*> FourierMotzkinConf::applyRule_(
    Lhs const& lhs, unsigned lhsVarBank,
    Rhs const& rhs, unsigned rhsVarBank,
    AbstractingUnifier& uwa
    ) const 
{
#define __ALASCA_Inferences_FM_DERIVE_EQUALITIES 1

  TIME_TRACE("fourier motzkin")
  auto cnst = uwa.computeConstraintLiterals();
  auto sigma = [&](auto t, auto bank) { return uwa.subs().apply(t,bank); };


  return lhs.numTraits().apply([&](auto numTraits) {
    using NumTraits = decltype(numTraits);




#define check_side_condition(cond, cond_code)                                                       \
    if (!(cond_code)) {                                                                             \
      DEBUG_FM(1, "side condition not fulfilled: " cond)                                            \
      return Option<Clause*>();                                                                     \
    }                                                                                               \

    check_side_condition("literals are of the same sort",
        lhs.numTraits() == rhs.numTraits()) // <- we must make this check because variables are unsorted
   
    ASS(lhs.sign() == Sign::Pos)
    ASS(rhs.sign() == Sign::Neg)
    ASS_EQ(lhs.sort(), rhs.sort())
    ASS(lhs.literal()->functor() == NumTraits::geqF()
     || lhs.literal()->functor() == NumTraits::greaterF())
    ASS(rhs.literal()->functor() == NumTraits::geqF()
     || rhs.literal()->functor() == NumTraits::greaterF())

    bool tight = lhs.literal()->functor() == NumTraits::geqF()
              && rhs.literal()->functor() == NumTraits::geqF();

    Stack<Literal*> out( lhs.clause()->size() - 1 // <- C1
                       + rhs.clause()->size() - 1 // <- C2
                       + 1                        // <- k t₁ + j t₂ > 0
#if __ALASCA_Inferences_FM_DERIVE_EQUALITIES
                       + (tight ? 1 : 0)          // <- -k s₂ + t₂ ≈ 0
#endif // __ALASCA_Inferences_FM_DERIVE_EQUALITIES
                       + cnst->size());      // Cnst

    auto s1 = lhs.selectedAtom();
    auto s2 = rhs.selectedAtom();

    ASS(!NumTraits::isFractional() || (!s1.isVar() && !s2.isVar()))

    // check_side_condition(
    //     "s₁, s₂ are not variables",
    //     !lhs.monom().isVar() && !rhs.monom().isVar())

    auto L1σ = sigma(lhs.literal(), lhsVarBank);
    check_side_condition( 
        "(+j s₁ + t₁ >₁ 0)σ /⪯ C₁σ",
        lhs.contextLiterals()
           .all([&](auto L) {
             auto Lσ = sigma(L, lhsVarBank);
             out.push(Lσ);
             return _shared->notLeq(L1σ, Lσ);
           }));


    auto L2σ = sigma(rhs.literal(), rhsVarBank);
    check_side_condition(
        "(-k s₂ + t₂ >₂ 0)σ /≺ C₂σ",
        rhs.contextLiterals()
           .all([&](auto L) {
             auto Lσ = sigma(L, rhsVarBank);
             out.push(Lσ);
             return _shared->notLess(L2σ, Lσ);
           }));


    auto s1σ = sigma(s1, lhsVarBank);
    auto s2σ = sigma(s2, rhsVarBank);
    // ASS_REP(_shared->norm().equivalent(sσ.term(), s2σ().term()), make_pair(sσ, s2σ()))
    Stack<TermList> t1σ(rhs.nContextTerms());
    Stack<TermList> t2σ(lhs.nContextTerms());

    check_side_condition(
        "s₁σ /⪯ t₁σ",
        lhs.contextTerms<NumTraits>()
           .all([&](auto ti) {
             auto tiσ = sigma(ti.factors->denormalize(), lhsVarBank);
             t1σ.push(NumTraits::mulSimpl(ti.numeral, tiσ));
             return _shared->notLeq(s1σ, tiσ);
           }))

    check_side_condition(
        "s₂σ /⪯ t₂σ ",
        rhs.contextTerms<NumTraits>()
           .all([&](auto ti) {
             auto tiσ = sigma(ti.factors->denormalize(), rhsVarBank);
             t2σ.push(NumTraits::mulSimpl(ti.numeral, tiσ));
             return _shared->notLeq(s2σ, tiσ);
           }))

    // DEBUG_FM(1, "(+j s₁ + t₁ >₁ 0)σ = ", *L1σ)
    // DEBUG_FM(1, "(-k s₂ + t₂ >₂ 0)σ = ", *L2σ)
    // check_side_condition(
    //     "( -k s₂ + t₂ >₂ 0 )σ /⪯  ( +j s₁ + t₁ >₁ 0 )σ",
    //     _shared->notLeq(L2σ, L1σ));

    auto j = lhs.numeral().unwrap<typename NumTraits::ConstantType>();
    auto k = rhs.numeral().unwrap<typename NumTraits::ConstantType>().abs();

    auto add = [](auto l, auto r) {
      return l == NumTraits::zero() ? r 
           : r == NumTraits::zero() ? l
           : NumTraits::add(l, r); };

    auto resolventTerm // -> (k t₁ + j t₂)σ
        = add( NumTraits::mulSimpl(k, NumTraits::sum(t1σ.iterFifo())),
               NumTraits::mulSimpl(j, NumTraits::sum(t2σ.iterFifo())));

    if (std::is_same<IntTraits, NumTraits>::value) {
      resolventTerm = add(resolventTerm, NumTraits::constantTl(-1));
    }

#if __ALASCA_Inferences_FM_DERIVE_EQUALITIES
    // (k t₁ + j t₂ > 0)σ
    out.push(NumTraits::greater(true, resolventTerm, NumTraits::zero()));

    if (tight) {
      auto rhsSum = // -> (-k s₂ + t₂)σ
        sigma(rhs.literal(), rhsVarBank)->termArg(0);
      out.push(NumTraits::eq(true, rhsSum, NumTraits::zero()));
    }
#else 
                   // (k t₁ + j t₂ >= 0)σ
    out.push(tight ? NumTraits::geq    (true, resolventTerm, NumTraits::zero())
                   // (k t₁ + j t₂ > 0)σ
                   : NumTraits::greater(true, resolventTerm, NumTraits::zero()));

#endif

    out.loadFromIterator(cnst->iterFifo());

    Inference inf(GeneratingInference2(Kernel::InferenceRule::ALASCA_FOURIER_MOTZKIN, lhs.clause(), rhs.clause()));
    auto cl = Clause::fromStack(out, inf);
    DEBUG_FM(1, "out: ", *cl);
    return Option<Clause*>(cl);
  });
}

} // namespace ALASCA 
} // namespace Inferences 

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
 * @file InequalityStrengthening.cpp
 * Implements class InequalityStrengthening.
 */

#include "InequalityStrengthening.hpp"
#include "Indexing/IndexManager.hpp"
#include "Kernel/LASCA.hpp"
#include "Saturation/SaturationAlgorithm.hpp"
#include "Shell/Statistics.hpp"
#include "Debug/TimeProfiling.hpp"

#define DEBUG(...) //DBG(__VA_ARGS__)

namespace Inferences {
namespace LASCA {

////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// INDEXING STUFF
////////////////////////////////////////////////////////////////////////////////////////////////////////////////

void InequalityStrengthening::attach(SaturationAlgorithm* salg) 
{
  GeneratingInferenceEngine::attach(salg);

  ASS(!_lhsIndex);
  ASS(!_rhsIndex);

  _lhsIndex = static_cast<decltype(_lhsIndex)>(_salg->getIndexManager()->request(Indexing::LASCA_IS_INT_RESOLUTION_LHS_SUBST_TREE));
  _rhsIndex = static_cast<decltype(_rhsIndex)>(_salg->getIndexManager()->request(Indexing::LASCA_INEQUALITY_STRENGTHENING_RHS));
  _rhsIndex->setShared(_shared);
  _lhsIndex->setShared(_shared);
}

void InequalityStrengthening::detach() 
{
  ASS(_salg);
  GeneratingInferenceEngine::detach();
}

#if VDEBUG
void InequalityStrengthening::setTestIndices(Stack<Indexing::Index*> const& indices)
{
  _lhsIndex = (decltype(_lhsIndex)) indices[0]; 
  _rhsIndex = (decltype(_rhsIndex)) indices[1]; 
  _lhsIndex->setShared(_shared);
  _rhsIndex->setShared(_shared);
}
#endif

using Lhs = InequalityStrengthening::Lhs;
using Rhs = InequalityStrengthening::Rhs;

ClauseIterator InequalityStrengthening::generateClauses(Clause* premise) 
{
  // // TODO refactor so this function is not copied and pasted among all unifying lasca rules
  // ASS(_lhsIndex)
  // ASS(_rhsIndex)
  // ASS(_shared)
  // Stack<Clause*> out;
  //
  // for (auto const& lhs : Lhs::iter(*_shared, premise)) {
  //   DEBUG("lhs: ", lhs)
  //   for (auto rhs_sigma : _rhsIndex->find(lhs.key())) {
  //     auto& rhs   = *rhs_sigma.data;
  //     auto& sigma = rhs_sigma.unifier;
  //     DEBUG("  rhs: ", rhs)
  //     auto res = applyRule(lhs, 0, rhs, 1, *sigma);
  //     if (res.isSome()) {
  //       out.push(res.unwrap());
  //     }
  //   }
  // }
  //
  // for (auto const& rhs : Rhs::iter(*_shared, premise)) {
  //   DEBUG("rhs: ", rhs)
  //
  //   for (auto lhs_sigma : _lhsIndex->find(rhs.key())) {
  //     auto& lhs   = *lhs_sigma.data;
  //     auto& sigma = lhs_sigma.unifier;
  //     if (lhs.clause() != premise) { // <- self application. the same one has been run already in the previous loop
  //       DEBUG("  lhs: ", lhs)
  //       auto res = applyRule(lhs, 1, rhs, 0, *sigma);
  //       if (res.isSome()) {
  //         out.push(res.unwrap());
  //       }
  //     }
  //   }
  // }
  //
  // return pvi(arrayIter(std::move(out)));
}

Option<Clause*> InequalityStrengthening::applyRule(
    Lhs const& lhs, unsigned lhsVarBank,
    Rhs const& rhs, unsigned rhsVarBank,
    AbstractingUnifier& uwa
    ) const 
{
  return lhs.numTraits().apply([&](auto numTraits) {
    return applyRule(numTraits, lhs, lhsVarBank, rhs, rhsVarBank, uwa);
  });
}


template<class NumTraits>
Option<Clause*> InequalityStrengthening::applyRule(NumTraits,
    Lhs const& lhs, unsigned lhsVarBank,
    Rhs const& rhs, unsigned rhsVarBank,
    AbstractingUnifier& uwa
    ) const 
{


  TIME_TRACE("inequality strengthening")

#define check_side_condition(cond, cond_code)                                                       \
    if (!(cond_code)) {                                                                             \
      DEBUG("side condition not fulfiled: " cond)                                                   \
      return Option<Clause*>();                                                                     \
    }                                                                                               \

    check_side_condition("literals are of the same sort",
        lhs.numTraits() == rhs.numTraits()) // <- we must make this check because variables are unsorted
   
    ASS_EQ(lhs.symbol(), LascaPredicate::IS_INT_POS)
    ASS_EQ(rhs.symbol(), LascaPredicate::GREATER)
    ASS_EQ(lhs.sort(), rhs.sort())
    auto cnst = uwa.computeConstraintLiterals();
    auto sigma = [&](auto t, auto bank) { return uwa.subs().apply(t, bank); };

    Stack<Literal*> out( lhs.clause()->size() - 1 // <- C1
                       + rhs.clause()->size() - 1 // <- C2
                       + 2                        // <- k s t₂ + k/j >= 0 \/ ~isInt((j/k) t₂ - t₁)
                       + cnst->size());      // Cnst


    auto jAbs = lhs.numeral().unwrap<typename NumTraits::ConstantType>().abs();
    auto timesJSign = [&](TermList t) -> TermList {
      switch (lhs.numeral().unwrap<typename NumTraits::ConstantType>().sign()) {
        case Sign::Pos: return t;
        case Sign::Neg: return NumTraits::minus(t);
        case Sign::Zero: ASSERTION_VIOLATION;
      }
      ASSERTION_VIOLATION
    };
    auto k = rhs.numeral().unwrap<typename NumTraits::ConstantType>();

    auto L1σ = sigma(lhs.literal(), lhsVarBank);
    check_side_condition( 
        "isInt(j s₁ + t₁)σ /⪯ C₁σ",
        lhs.contextLiterals()
           .all([&](auto L) {
             auto Lσ = sigma(L, lhsVarBank);
             out.push(Lσ);
             return _shared->notLeq(L1σ, Lσ);
           }));


    auto L2σ = sigma(rhs.literal(), rhsVarBank);
    check_side_condition(
        "(k s₂ + t₂ > 0)σ /≺ C₂σ",
        rhs.contextLiterals()
           .all([&](auto L) {
             auto Lσ = sigma(L, rhsVarBank);
             out.push(Lσ);
             return _shared->notLess(L2σ, Lσ);
           }));


    auto s1σ = sigma(lhs.monom(), lhsVarBank);
    auto s2σ = sigma(rhs.monom(), rhsVarBank);
    // ASS_REP(_shared->equivalent(sσ.term(), s2σ().term()), make_pair(sσ, s2σ()))
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

    auto add = [](auto l, auto r) {
      return l == NumTraits::zero() ? r 
           : r == NumTraits::zero() ? l
           : NumTraits::add(l, r); };

    auto resolventTerm // -> ((j / k) t₂ -  t₁)σ
        = add( NumTraits::mulSimpl((jAbs / k), NumTraits::sum(t2σ.iterFifo())),
               NumTraits::minus(timesJSign(NumTraits::sum(t1σ.iterFifo()))));

    // ~isInt((j / k) t₂ -  t₁)σ
    out.push(NumTraits::isInt(false, resolventTerm));
    // ~isInt(k s₂ + t₂ - (k / j) >= 0)σ
    out.push(NumTraits::geq(true, NumTraits::add(
            sigma(rhs.ircLiteral().apply([](auto l) { return l.denormalize(); })->termArg(0), rhsVarBank), 
            NumTraits::constantTl(-k / jAbs)), NumTraits::zero()));

    out.loadFromIterator(cnst->iterFifo());

    Inference inf(GeneratingInference2(Kernel::InferenceRule::LASCA_INEQUALITY_STRENGTHENING, lhs.clause(), rhs.clause()));
    auto cl = Clause::fromStack(out, inf);
    DEBUG("out: ", *cl);
    return Option<Clause*>(cl);
}

} // namespace LASCA 
} // namespace Inferences 

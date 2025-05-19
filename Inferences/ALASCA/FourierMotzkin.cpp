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
#include "Saturation/SaturationAlgorithm.hpp"
#include "Shell/Statistics.hpp"
#include "Debug/TimeProfiling.hpp"

#define DEBUG_FM(lvl, ...) if (lvl < 0) { DBG(__VA_ARGS__) }

namespace Inferences {
namespace ALASCA {


Clause* FourierMotzkinConf::applyRule_(
    Lhs const& lhs_, unsigned lhsVarBank,
    Rhs const& rhs_, unsigned rhsVarBank,
    AbstractingUnifier& uwa
    ) const 
{

  TIME_TRACE("fourier motzkin")
  auto cnst = uwa.computeConstraintLiterals();
  auto sigma = [&](auto t, auto bank) { return uwa.subs().apply(t,bank); };


  return lhs_.apply([&](auto lhs) {
    auto& rhs = rhs_.template unwrap<decltype(lhs)>();
    using NumTraits = decltype(lhs.numTraits());

    bool tight = lhs.literal()->functor() == NumTraits::geqF()
              && rhs.literal()->functor() == NumTraits::geqF();

    // auto s1 = lhs.selectedAtomicTerm();
    // auto s2 = rhs.selectedAtomicTerm();
    // ASS(!NumTraits::isFractional() || (!s1.isVar() && !s2.isVar()))

    auto j = lhs.numeral();
    auto k = rhs.numeral().abs();

    auto add = [](auto l, auto r) {
      return l == NumTraits::zero() ? r 
           : r == NumTraits::zero() ? l
           : NumTraits::add(l, r); };

    auto resolventTerm // -> (k t₁ + j t₂)σ
        = add( NumTraits::mulSimpl(k, sigma(lhs.contextTermSum(), lhsVarBank)),
               NumTraits::mulSimpl(j, sigma(rhs.contextTermSum(), rhsVarBank)));


    // TODO 4 do we need to remove this?
    if (std::is_same<IntTraits, NumTraits>::value) {
      resolventTerm = add(resolventTerm, NumTraits::constantTl(-1));
    }

    auto cl = Clause::fromIterator(concatIters(
            /* (k t₁ + j t₂ > 0)σ */ 
            iterItems(NumTraits::greater(true, resolventTerm, NumTraits::zero())),
            /* (-k s₂ + t₂)σ = 0 */
            someIf(tight, [&]() { 
              auto rhsSum = sigma(rhs.literal(), rhsVarBank)->termArg(0);
              return NumTraits::eq(true, rhsSum, NumTraits::zero()); 
            }).intoIter(),
            lhs.contextLiterals().map([&](auto l) { return sigma(l, lhsVarBank); }),
            rhs.contextLiterals().map([&](auto l) { return sigma(l, rhsVarBank); }),
            arrayIter(cnst).cloned()
          ), Inference(GeneratingInference2(Kernel::InferenceRule::ALASCA_FOURIER_MOTZKIN, lhs.clause(), rhs.clause())));

    DEBUG_FM(1, "out: ", *cl);
    return cl;
  });
}

} // namespace ALASCA 
} // namespace Inferences 

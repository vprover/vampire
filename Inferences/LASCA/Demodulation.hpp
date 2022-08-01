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
 * @file Demodulation.hpp
 *
 * Shared code between  FwdDemodulation and BwdDemodulation.
 */

#ifndef __LASCA_Demodulation__
#define __LASCA_Demodulation__

#include "Forwards.hpp"
#include "Inferences/InferenceEngine.hpp"
#include "Kernel/LASCA.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/FormulaVarIterator.hpp"
#include "Shell/Statistics.hpp"
#include "Kernel/LaLpo.hpp"

#define UNIMPLEMENTED ASSERTION_VIOLATION

namespace Inferences {
namespace LASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class Demodulation
{
public:
  CLASS_NAME(Demodulation);
  USE_ALLOCATOR(Demodulation);

  // ±ks + t ≈ 0          C[sσ]
  // ============================
  //         C[sσ -> (∓ (1/k) t)σ]
  // where
  // • sσ ≻ tσ 
  // • C[sσ] ≻ (±ks + t ≈ 0)σ

  struct Lhs : public SelectedEquality {
    Lhs(SelectedEquality self) : SelectedEquality(std::move(self)) {}

    static auto iter(LascaState& shared, Clause* simplifyWith) {
      return iterTraits(getSingletonIterator(simplifyWith))
        .filter([](Clause* cl) { return cl->size() == 1 && (*cl)[0]->isEquality() && (*cl)[0]->isPositive(); })
        .flatMap([&](Clause* cl) 
            { return shared.selectedEqualities(cl, 
                /* literals */ SelectionCriterion::ANY, 
                /* terms */    SelectionCriterion::STRICTLY_MAX,
                /* unshielded vars */ false); })
        .map([](auto x) { return Lhs(std::move(x)); })
        .timeTraced("lasca demodulation lhs");
    }
  };

  struct Rhs {
    TermList term;
    Clause* clause;
    auto key() const { return term; }
    auto sort() const { return SortHelper::getResultSort(term.term()); }
    auto asTuple() const { return std::tie(term, clause); }
    IMPL_COMPARISONS_FROM_TUPLE(Rhs)

    friend std::ostream& operator<<(std::ostream& out, Rhs const& self)
    { return out << self.clause << "[ " << self.term << " ]"; }

    static auto iter(LascaState& shared, Clause* cl) 
    {
      // TIME_TRACE("lasca demodulation rhs")
      return iterTraits(cl->iterLits())
        .flatMap([cl](Literal* lit) {

          return pvi(iterTraits(vi(new SubtermIterator(lit)))
              // TODO filter our things that can never be rewritten 
            // .filter([](TermList t) {
            //   if (t.isTerm()) {
            //     auto term = t.term();
            //     return forAnyNumTraits([&](auto numTraits){
            //         using NumTraits = decltype(numTraits);
            //         return SortHelper::getResultSort(term) == NumTraits::sort()
            //             && !NumTraits::isNumeral(term)
            //             && !(NumTraits::mulF() == term->functor() && NumTraits::isNumeral(*term->nthArgument(0)) );
            //                     // ^^^ term = k * t
            //     });
            //   } else {
            //     return false; 
            //   }
            // })
            .filter([](TermList t) { return t.isTerm(); })
            .map([=](TermList t) { return Rhs { .term = t, .clause = cl, }; }));
        })
      .timeTraced("lasca demodulation rhs");

    }
  };

 
  template<class Sigma> 
  static Option<Clause*> apply(
                      LascaState& shared,
                      Lhs lhs,               // <- { ±ks + t ≈ 0 }
                      Rhs rhs,                    // <- C[sσ]
                      Sigma sigma);

  // ±ks + t ≈ 0          C[sσ]
  // ============================
  //         C[sσ -> (∓ (1/k) t)σ]
  // where
  // • sσ ≻ tσ 
  // • C[sσ] ≻ (±ks + t ≈ 0)σ
  template<class _NumTraits>
  struct Simplification {
    using NumTraits = _NumTraits;
    //Clause*               clause;  // <- { ±ks + t ≈ 0  }
    LascaLiteral<NumTraits> lit;     // <- ±ks + t ≈ 0 
    Monom<NumTraits>      monom;   // <- ±ks 
  };

  using AnySimplification = Coproduct<Simplification<RatTraits>, Simplification<RealTraits>>;

  static auto simplifiers(LascaState& shared, Clause* simplifyWith) {
    return iterTraits(getSingletonIterator(simplifyWith))
      .filter([](Clause* cl) { return cl->size() == 1 && (*cl)[0]->isEquality() && (*cl)[0]->isPositive(); })
      .flatMap([&](Clause* cl) 
          { return shared.selectedEqualities(cl, 
              /* literals */ SelectionCriterion::ANY, 
              /* terms */    SelectionCriterion::STRICTLY_MAX,
              /* unshielded vars */ false); });
  }


};





// ±ks + t ≈ 0              C[sσ]
// ==============================
//       C[sσ -> (∓ (1/k) t)σ]
// where
// • sσ ≻ tσ 
// • C[sσ] ≻ (±ks + t ≈ 0)σ
//
template<class Sigma> 
Option<Clause*> Demodulation::apply(
                      LascaState& shared,
                      Lhs lhs,  // <- { ±ks + t ≈ 0 }
                      Rhs rhs,  // <- C[sσ]
                      Sigma sigma)
{
  TIME_TRACE("lasca demodulation")
  auto nothing = [&]() { return Option<Clause*>(); };
  ASS(lhs.clause()->size() == 1)
  ASS(lhs.literal()->isEquality())
  ASS(lhs.literal()->isPositive())
  ASS(sigma(lhs.biggerSide()) == rhs.term)

  // TODO i think this assertion always holds due to the QKBO properties on the ground level, but the impl might return incomparable if the lifting's too weak
  // ASS_REP(shared.ordering->compare(lhs.biggerSide(), lhs.smallerSide()) == Ordering::Result::GREATER, lhs)

  // checking `C[sσ] ≻ (±ks + t ≈ 0)σ`
  {
    auto lhs_sigma = sigma(lhs.literal());
    auto greater = iterTraits(rhs.clause->iterLits())
      .any([&](auto lit) 
          { return shared.greater(lit, lhs_sigma); });
    if (!greater)  {
      return nothing();
    }
  }

  auto replacement = sigma(lhs.smallerSide());

  auto lits = iterTraits(rhs.clause->iterLits())
    .map([&](auto lit) { return EqHelper::replace(lit, rhs.term, replacement); })
    .template collect<Stack>();

  Inference inf(SimplifyingInference2(Kernel::InferenceRule::LASCA_FWD_DEMODULATION, lhs.clause(), rhs.clause));
  return Option<Clause*>(Clause::fromStack(lits, inf));
}

} // namespace LASCA
} // namespace Inferences

#endif /*__LASCA_Demodulation__*/

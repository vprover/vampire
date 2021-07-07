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
 * @file DemodulationModLA.hpp
 *
 * Shared code between  FwdDemodulationModLA and BwdDemodulationModLA.
 */

#ifndef __IRC_DemodulationModLA__
#define __IRC_DemodulationModLA__

#include "Forwards.hpp"
#include "Inferences/InferenceEngine.hpp"
#include "Kernel/IRC.hpp"
#include "Kernel/EqHelper.hpp"

#define UNIMPLEMENTED ASSERTION_VIOLATION

namespace Inferences {
namespace IRC {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class DemodulationModLA
{
public:
  CLASS_NAME(DemodulationModLA);
  USE_ALLOCATOR(DemodulationModLA);

  // ±ks + t ≈ 0          C[sσ]
  // ============================
  //         C[sσ -> (∓ (1/k) t)σ]
  // where
  // • sσ is strictly max. in terms(s + t)σ 
  // • C[sσ] ≻ (±ks + t ≈ 0)σ
 
  template<class NumTraits, class Sigma> 
  static Option<Clause*> apply(
                        IrcState& shared,
                        Clause* Hyp1,                    // <- { ±ks + t ≈ 0 }
                        Clause* C,                       // <- C[sσ]
                        IrcLiteral<NumTraits> ks_t, // <- ±ks + t ≈ 0
                        TermList s,
                        Perfect<MonomFactors<NumTraits>> s_norm,
                        Sigma sigma);
 
  template<class Sigma> 
  static Option<Clause*> apply(
                        IrcState& shared,
                        Clause* Hyp1,                    // <- { ±ks + t ≈ 0 }
                        Clause* C,                       // <- C[sσ]
                        IrcLiteral<IntTraits> ks_t, // <- ±ks + t ≈ 0
                        TermList s,
                        Perfect<MonomFactors<IntTraits>> s_norm,
                        Sigma sigma)
  { ASSERTION_VIOLATION }

  struct SimplifyablePosition {
    Literal* lit;
    TermList term;
  };

  static auto simplifyablePositions(IrcState& shared, Clause* toSimplify) 
  {
    CALL("BwdDemodulationModLAIndex::handleClause");
  
    return iterTraits(toSimplify->iterLits())
      .flatMap([](Literal* lit) {

        return pvi(iterTraits(vi(new SubtermIterator(lit)))
          .filter([](TermList t) {
            if (t.isTerm()) {
              auto term = t.term();
              return forAnyNumTraits([&](auto numTraits){
                  using NumTraits = decltype(numTraits);
                  return SortHelper::getResultSort(term) == NumTraits::sort()
                      && !NumTraits::isNumeral(term)
                      && !(NumTraits::mulF() == term->functor() && NumTraits::isNumeral(*term->nthArgument(0)) );
                              // ^^^ term = k * t
              });
            } else {
              return false; 
            }
          })
          .map([lit](TermList term) 
                     { return SimplifyablePosition { .lit = lit, .term = term, }; }));
      });
  }

  // ±ks + t ≈ 0          C[sσ]
  // ============================
  //         C[sσ -> (∓ (1/k) t)σ]
  // where
  // • sσ is strictly max. in terms(s + t)σ 
  // • C[sσ] ≻ (±ks + t ≈ 0)σ
  template<class _NumTraits>
  struct Simplification {
    using NumTraits = _NumTraits;
    //Clause*               clause;  // <- { ±ks + t ≈ 0  }
    IrcLiteral<NumTraits> lit;     // <- ±ks + t ≈ 0 
    Monom<NumTraits>      monom;   // <- ±ks 
  };

  using AnySimplification = Coproduct<Simplification<RatTraits>, Simplification<RealTraits>>;

  template<class NumTraits>
  static auto __simplifiers(IrcState& shared, Clause* simplifyWith, IrcLiteral<NumTraits> lit)
  {
    return pvi(iterTraits(ownedArrayishIterator(shared.maxAtomicTerms(lit, /* strictlyMax */ true)))
      .map([lit](auto monom) { 
          return AnySimplification(Simplification<NumTraits> {
            // .clause = simplifyWith,
            .lit    = lit,
            .monom  = monom,
          });
      }));
  }


  static auto __simplifiers(IrcState& shared, Clause* simplifyWith, IrcLiteral<IntTraits> lit)
  { return pvi(VirtualIterator<AnySimplification>::getEmpty()); }

  static auto simplifiers(IrcState& shared, Clause* simplifyWith) {
    ASS(&shared)
    return iterTraits(getSingletonIterator(simplifyWith))
      .filter([](Clause* cl) { return cl->size() == 1 && (*cl)[0]->isEquality() && (*cl)[0]->isPositive(); })
      .filterMap([&](Clause* simplifyWith) 
          { return shared.normalize((*simplifyWith)[0]); })
      .flatMap([&shared, simplifyWith](AnyIrcLiteral lit) {
          return lit.apply([&shared, simplifyWith](auto lit) 
              { return __simplifiers(shared, simplifyWith, lit); });
      });
  }


};





// ±ks + t ≈ 0              C[sσ]
// ==============================
//       C[sσ -> (∓ (1/k) t)σ]
// where
// • sσ is strictly max. in terms(s + t)σ 
// • C[sσ] ≻ (±ks + t ≈ 0)σ
//
template<class NumTraits, class Sigma> 
Option<Clause*> DemodulationModLA::apply(
                      IrcState& shared,
                      Clause* C,                  // <- C[sσ]
                      Clause* Hyp1,               // <- { ±ks + t ≈ 0 }
                      IrcLiteral<NumTraits> ks_t, // <- ±ks + t ≈ 0
                      TermList s,
                      Perfect<MonomFactors<NumTraits>> s_norm,
                      Sigma sigma)
{
  Option<Clause*> nothing;
  ASS(Hyp1->size() == 1)
  ASS((*Hyp1)[0]->isEquality())
  ASS((*Hyp1)[0]->isPositive())

  // checking `C[sσ] ≻ (±ks + t ≈ 0)σ`
  {
    auto ks_t_sigma = sigma((*Hyp1)[0]);
    for (auto lit : iterTraits(C->iterLits())) {
      auto lit_sigma = sigma(lit);
      auto cmp = shared.ordering->compare(lit_sigma, ks_t_sigma);
      if (cmp != Ordering::Result::GREATER) {
        return nothing;
      }
    }
  }

  auto k = ks_t.term().iterSummands()
             .find([&](auto monom) { return monom.factors == s_norm; })
             .unwrap().numeral;

  auto replacement =  // <- (∓ (1/k) t)σ
    sigma(NumTraits::sum( 
      ks_t.term().iterSummands()
       .filter([&](auto monom) { return monom.factors != s_norm; })
       .map([&](auto monom) { return (monom / -k).denormalize(); })));
     

  auto s_sigma = sigma(s);
  auto lits = iterTraits(C->iterLits())
    .map([&](auto lit) { return EqHelper::replace(lit, s_sigma, replacement); })
    .template collect<Stack>();

  Inference inf(SimplifyingInference2(Kernel::InferenceRule::IRC_FWD_DEMODULATION, Hyp1, C));
  return Option<Clause*>(Clause::fromStack(lits, inf));
}

} // namespace IRC
} // namespace Inferences

#endif /*__IRC_DemodulationModLA__*/

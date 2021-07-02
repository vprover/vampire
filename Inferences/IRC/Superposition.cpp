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
#include "Saturation/SaturationAlgorithm.hpp"
#include "Shell/Statistics.hpp"
#include "Kernel/EqHelper.hpp"

#define ORDERING_ASSERTIONS 0 // TODO <- implement
#if ORDERING_ASSERTIONS 
#  define ORD_CHECK(...) ASS(__VA_ARGS__)
#else 
#  define ORD_CHECK(...) if (!(__VA_ARGS__)) return nothing;
#endif // ORDERING_ASSERTIONS

namespace Inferences {
namespace IRC {

void Superposition::attach(SaturationAlgorithm* salg) 
{ 
  CALL("Superposition::attach");
  ASS(!_index);

  GeneratingInferenceEngine::attach(salg);
  _index=static_cast<IRCSuperpositionIndex*> (
	  _salg->getIndexManager()->request(IRC_SUPERPOSITION_SUBST_TREE) );
  _index->setShared(_shared);
}

void Superposition::detach() 
{
  CALL("Superposition::detach");
  ASS(_salg);

  _index=0;
  _salg->getIndexManager()->release(IRC_SUPERPOSITION_SUBST_TREE);
  GeneratingInferenceEngine::detach();
}

ClauseIterator Superposition::generateClauses(Clause* premise) 
{

  // auto maxLits = 
  auto maxLits = make_shared(new Stack<Literal*>(_shared->strictlyMaxLiterals(premise)));
  return pvi(numTraitsIter([this, premise, maxLits](auto numTraits) {
     using NumTraits = decltype(numTraits);
     return iterTraits(ownedArrayishIterator(_shared->maxAtomicTermsNonVar<NumTraits>(premise)))
       .filter([maxLits](auto maxTerm) 
           { return iterTraits(maxLits->iterFifo())
                      .find([&](auto x) 
                          { return x == maxTerm.literal; })
                      .isSome(); })
       .filterMap([this, premise](auto maxTerm) { return this->generateClauses(premise, maxTerm.literal, maxTerm.ircLit, maxTerm.self); })
       .flatten();
  }));
  // return pvi(
  //     iterTraits(ownedArrayishIterator(_shared->strictlyMaxLiterals(premise)))
  //     .filterMap([this, premise](auto lit) -> Option<ClauseIterator> {
  //       return _shared->normalize(lit)
  //       .andThen([this, premise, lit](auto unsortedLit) -> Option<ClauseIterator> {
  //           return unsortedLit.apply([this, premise, lit](auto sortedLit) { return this->generateClauses(premise, lit, sortedLit); });
  //         });
  //       })
  //     .flatten());
}

  

#if VDEBUG
void Superposition::setTestIndices(Stack<Indexing::Index*> const& indices) 
{
  _index = (IRCSuperpositionIndex*) indices[0]; 
  _index->setShared(_shared);
}
#endif

// C1 \/ ±ks1+t1 ≈ 0            C2 \/ u[s2]+t2 <> 0
// ================================================
//   (C1 \/ C2 \/ u[∓(1/k)t1]+t2 <> 0) σ \/ Cnst
// where
// • uwa(s1,s2)=⟨σ,Cnst⟩
// • <>  ∈ {>,≥,≈,̸≈}
// •        s1  σ is strictly maximal in terms(s1 + t1)σ
// • term(u[s2])σ is strictly maximal in terms(u[s2] + t2)σ 
// • (±k. s1 + t1 ≈ 0)σ is strictly maximal in Hyp1σ
// • ( u[s2] + t2 ≈ 0)σ is strictly maximal in Hyp2σ
// • Hyp2σ is strictly maximal in {Hyp1, Hyp2}σ.

template<class NumTraits> Option<ClauseIterator> Superposition::generateClauses(
    Clause* hyp1,            // <- `C1 \/ ±ks1+t1 ≈ 0` 
    Literal* pivot1,         // <-       `±ks1+t1 ≈ 0` 
    IrcLiteral<NumTraits> eq,// <-       `±ks1+t1 ≈ 0` 
    Monom<NumTraits> k_s1    // <-       `±ks1` 
    ) const 
{
  using Numeral = typename NumTraits::ConstantType;
  if (eq.symbol() != IrcPredicate::EQ) {
    return Option<ClauseIterator>();
  }
  return Option<ClauseIterator>(
      // pvi(iterTraits(ownedArrayishIterator(_shared->maxAtomicTerms(eq)))
      //   .flatMap([=](auto k_s1) { 
          // return
          pvi(iterTraits(pvi(this->_index->getUnificationsWithConstraints(k_s1.factors->denormalize(), true)))
              .filterMap([=](TermQueryResult res) -> Option<Clause*> {
                Stack<UnificationConstraint> dummy;
                Option<Clause*> nothing;

                auto hyp2 = res.clause;    // <- `C2 \/ u[s2]+t2 <> 0`
                auto pivot2 = res.literal; // <-       `u[s2]+t2 <> 0`
                auto s2 = res.term; 
                auto s1 = k_s1.factors; 
                auto& cnst = res.constraints ? *res.constraints : dummy;
                auto sigma = [&](auto term, int varBank) { return res.substitution->applyTo(term, varBank); };

                // TODO maximality check after unification
                // maximality checks
                {
                  // • ±k. s1 + t1 ≈ 0 is strictly maximal in Hyp1
                  ORD_CHECK(_shared->strictlyMaximal(pivot1, hyp1->getLiteralIterator()))
                  // • (±k. s1 + t1 ≈ 0)σ is strictly maximal in Hyp1σ
                  ORD_CHECK(_shared->strictlyMaximal(sigma(pivot1, 0), iterTraits(hyp1->getLiteralIterator()).map([&](auto lit) { return sigma(lit, 0); })))

                  // • u[s2] + t2 ≈ 0 is strictly maximal in Hyp2
                  ORD_CHECK(_shared->strictlyMaximal(pivot2, hyp2->getLiteralIterator()))
                  // • ( u[s2] + t2 ≈ 0)σ is strictly maximal in Hyp2σ
                  ORD_CHECK(_shared->strictlyMaximal(sigma(pivot2, 1), iterTraits(hyp2->getLiteralIterator()).map([&](auto lit) { return sigma(lit, 1); })))

                  // •        s1  σ is strictly maximal in terms(s1 + t1)σ
                  ORD_CHECK(_shared->strictlyMaximal(sigma(s1->denormalize(), 0), eq.term().iterSummands().map([&](auto monom) { return sigma(monom.factors->denormalize(), 0); })))

                  // • term(u[s2])σ is strictly maximal in terms(u[s2] + t2)σ 
                  // TODO check this condition somehow ?!
                }

                Stack<Literal*> concl(hyp1->size() - 1 // <- C1
                    + hyp2->size() - 1 // <- C2
                    + 1                // <- u[∓(1/k)t1]+t2 <> 0
                    + cnst.size());    // <- Cnst


                // adding C1
                for (auto lit : iterTraits(hyp1->getLiteralIterator())) {
                  if (lit != pivot1)
                    concl.push(sigma(lit, 0));
                }

                // adding C2
                for (auto lit : iterTraits(hyp2->getLiteralIterator())) {
                  if (lit != pivot2)
                    concl.push(sigma(lit, 1));
                }

                // adding u[∓(1/k)t1]+t2 <> 0) σ 
                {
                  auto t1 = NumTraits::sum(eq.term().iterSummands()
                      .filter([&](auto t) { return t != k_s1; })
                      .map([](auto monom) { return monom.denormalize(); }));
                  auto k = k_s1.numeral;
                  auto repl = 
                  //   ^^^^ -> u[∓(1/k)t1]+t2 <> 0) σ 
                      k != Numeral(-1) ? NumTraits::mul(NumTraits::constantTl(Numeral(-1) / k), sigma(t1, 0))
                                       :                                                        sigma(t1, 0) ;


                  auto resolvent = EqHelper::replace(sigma(pivot2, 1), sigma(s2, 1), repl);
                  concl.push(resolvent);
                }

                // adding Cnst
                concl.loadFromIterator(UwaResult::cnstLiterals(*res.substitution, cnst));

                env.statistics->ircSupCnt++;
                Inference inf(GeneratingInference2(Kernel::InferenceRule::IRC_SUPERPOSITION, hyp1, hyp2));
                return Option<Clause*>(Clause::fromStack(concl, inf));
              })
          )
  //           ;
  //
  //
  //       })
  // )
  ) ;
}

Option<ClauseIterator> Superposition::generateClauses(Clause* hyp1, Literal* pivot1, IrcLiteral<IntTraits> eq, Monom<Kernel::IntTraits>) const 
{ return Option<ClauseIterator>(); } 

} // namespace IRC 
} // namespace Inferences 

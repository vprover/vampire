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
 * @file LiteralFactoring.cpp
 * Defines class LiteralFactoring
 *
 */

#include "LiteralFactoring.hpp"

#define DEBUG(...) // DBG(__VA_ARGS__)

namespace Inferences {
namespace IRC {

void LiteralFactoring::attach(SaturationAlgorithm* salg) 
{ }

void LiteralFactoring::detach() 
{ }

//  C \/ ±js1 + t1 <> 0 \/ ±ks2 + t2 <> 0
// ====================================================
// (C \/ ±js1 + t1 <> 0 \/ k t1 − j t2  ̸≈ 0) σ \/ Cnst
//
//
// where
// • uwa(s1,s2)=⟨σ,Cnst⟩
// • <> ∈ {>,≥,≈, /≈}
// • term(s1)σ is maximal in ({s1} ∪ terms(t1))σ
// • term(s2)σ is maximal in ({s2} ∪ terms(t2))σ
// • (±ks1 + t1 <> 0)σ is maximal in Hypσ <- TODO
// • (±ks2 + t2 <> 0)σ is maximal in Hypσ <- TODO




template<class NumTraits>
Clause* LiteralFactoring::applyRule(Clause* premise, 
    Indexed<IrcLiteral<NumTraits>> l1,  Monom<NumTraits> j_s1,
    Indexed<IrcLiteral<NumTraits>> l2,  Monom<NumTraits> k_s2,
    UwaResult uwa)
{
  auto sigma = [&](auto x){ return uwa.sigma.apply(x, /* varbank */ 0); };
  auto& cnst  = uwa.cnst;
  auto j = j_s1.numeral;
  auto k = k_s2.numeral;
  auto s1 = j_s1.factors;
  auto s2 = k_s2.factors;

  auto pivotSum = 
  //   ^^^^^^^^--> `(k t1 − j t2)σ`
    NumTraits::sum(iterTraits(getConcatenatedIterator(
      l1->term().iterSummands()
        .filter([&](auto t) { return t != j_s1; })
        .map([&](auto t) { return  sigma((k * t).denormalize()); }),

      l2->term().iterSummands()
        .filter([&](auto t) { return t != k_s2; })
        .map([&](auto t) { return  sigma((-j * t).denormalize()); })
        )));

  auto pivotLiteral = NumTraits::eq(false, pivotSum, NumTraits::zero());

  Stack<Literal*> conclusion(premise->size() + cnst.size());
  for (unsigned i = 0; i < premise->size(); i++) {
    if (i != l2.idx)
      conclusion.push(sigma((*premise)[i]));
  }
  conclusion.push(sigma(pivotLiteral));
  conclusion.loadFromIterator(uwa.cnstLiterals());

  Inference inf(GeneratingInference1(Kernel::InferenceRule::IRC_LITERAL_FACTORING, premise));
  return Clause::fromStack(conclusion, inf);
}


template<class NumTraits>
ClauseIterator LiteralFactoring::generateClauses(Clause* premise, Indexed<IrcLiteral<NumTraits>> l1, Indexed<IrcLiteral<NumTraits>> l2)
{
  return pvi(iterTraits(ownedArrayishIterator(_shared->maxAtomicTerms(*l1)))
    .flatMap([=](auto j_s1) {
      return pvi(iterTraits(ownedArrayishIterator(_shared->maxAtomicTerms(*l2)))
        .filterMap([=](auto k_s2) { 
            auto s1 = j_s1.factors->denormalize();
            auto s2 = k_s2.factors->denormalize();
            return _shared->unify(s1, s2)
              .andThen([&](auto&& sigma_cnst) -> Option<UwaResult> { 
                  auto maxAfterUnif = [&](auto term, auto literal) {
                    auto term_sigma    = _shared->normalize(TypedTermList(sigma_cnst.sigma.apply(term, 0), NumTraits::sort()))
                      .downcast<NumTraits>().unwrap()
                      ->tryMonom().unwrap().factors;
                    auto literal_sigma = _shared->normalize(sigma_cnst.sigma.apply(literal.denormalize(), 0))
                                     .unwrap().template unwrap<IrcLiteral<NumTraits>>();
                    auto max = _shared->maxAtomicTerms(literal_sigma); // TODO can be done more efficient
                    return iterTraits(max.iterFifo()).any([&](auto monom) { return monom.factors == term_sigma; });
                  };

                  if (maxAfterUnif(s1, *l1) && maxAfterUnif(s1, *l1)) {
                    return Option<UwaResult>(std::move(sigma_cnst));
                  } else {
                    return Option<UwaResult>();
                  }
              })
              .map([&](auto sigma_cnst){ return applyRule(premise, l1, j_s1, l2, k_s2, std::move(sigma_cnst)); });
            }));
    }));
}

ClauseIterator LiteralFactoring::generateClauses(Clause* premise) 
{
  static_assert(std::is_same<ArrayishObjectIterator<Clause>, decltype(premise->getSelectedLiteralIterator())>::value, "we assume that the first numSelected() literals are the selected ones");

  DEBUG("in: ", *premise)

  auto normalize = [this,premise](unsigned i) {
      auto lit = (*premise)[i];
      auto norm = _shared->normalizer.normalize(lit);
      return norm.isSome() && !norm.unwrap().overflowOccurred
        ? Option<Indexed<AnyIrcLiteral>>(indexed(i, norm.unwrap().value))
        : Option<Indexed<AnyIrcLiteral>>();
  };

  return pvi(iterTraits(getRangeIterator((unsigned)0, premise->numSelected()))
    .filterMap([=](unsigned i) 
      { return normalize(i); })

    .flatMap([this, premise,normalize](auto l1) {
     return pvi(iterTraits(getRangeIterator(l1.idx + 1, premise->numSelected()))

       .filterMap([=](unsigned j)
         { return normalize(j); })

        /* check whether l1 and l2 are of the same number sort */
       .filter([=](auto l2) 
         { return (*l1).apply([&](auto l1) { return l2->template is<decltype(l1)>(); }); })

        /* check whether l1 and l2 have the same predicate symbol */
       .filter([=](auto l2) 
         { return (*l1).apply([&](auto l1) 
             { return l1.symbol() == l2->template unwrap<decltype(l1)>().symbol(); }); })

       .flatMap([=](auto l2) -> ClauseIterator {
           return (*l1).apply([&](auto l1_) -> ClauseIterator { 
               return generateClauses(premise, 
                   indexed(l1.idx, l1_), 
                   indexed(l2.idx, l2->template unwrap<decltype(l1_)>())); });
       }));
  }));
}

  

#if VDEBUG
void LiteralFactoring::setTestIndices(Stack<Indexing::Index*> const&) 
{

}
#endif

} // namespace IRC 
} // namespace Inferences 

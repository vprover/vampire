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
 * @file InequalityFactoring.cpp
 * Defines class InequalityFactoring
 *
 */

#include "InequalityFactoring.hpp"
#include "Debug/Assertion.hpp"
#include "Shell/Statistics.hpp"
#include "Debug/TimeProfiling.hpp"

#define DEBUG(...) // DBG(__VA_ARGS__)
#define FACTOR_NEGATIVE 0

namespace Inferences {
namespace ALASCA {

void InequalityFactoring::attach(SaturationAlgorithm* salg) { }

void InequalityFactoring::detach() { }


#define CHECK_CONDITION(name, condition)                                                            \
  if (!(condition)) {                                                                               \
    DEBUG("side condition not satisfied: " name)                                                    \
    return nothing();                                                                               \
  }                                                                                                 \

//  C \/ +j s1 + t1 >1 0 \/ +k s2 + t2 >2 0
// ====================================================
// (C \/ k t1 − j t2 >3 0 \/ +k s2 + t2 >2 0) σ \/ Cnst
//
//
// where
// • ⟨σ,Cnst⟩ = uwa(s1,s2)
// • >i ∈ {>,≥}
// • s1σ /⪯ terms(t1)σ
// • s2σ /⪯ terms(t2)σ
// •    (j s1 + t1 >1 0)σ /≺ (k s2 + t2 >2 0 \/ C)σ
//   or (k s2 + t2 >2 0)σ /≺ (j s1 + t1 >1 0 \/ C)σ
// • (>3) = if (>1, >2) = (>=, >) then (>=) 
//                                else (>)

template<class NumTraits>
Option<Clause*> InequalityFactoring::applyRule(
    SelectedAtomicTermItp<NumTraits> const& l1,  // +j s1 + t1 >1 0
    SelectedAtomicTermItp<NumTraits> const& l2   // +k s2 + t2 >2 0
    )
{
  TIME_TRACE("alasca inequality factoring application")
  DEBUG("l1: ", l1)
  DEBUG("l2: ", l2)

  auto nothing = [&]() { return Option<Clause*>{}; };

  auto s1 = l1.selectedAtom();
  auto s2 = l2.selectedAtom();
  auto uwa = _shared->unify(s1, s2);

  CHECK_CONDITION("⟨σ,Cnst⟩ = uwa(s1,s2)",
                  uwa.isSome())

  auto cnst  = uwa->computeConstraintLiterals();
  auto sigma = [&](auto x){ return uwa->subs().apply(x, /* varbank */ 0); };
  auto j = l1.numeral();
  auto k = l2.numeral();
  ASS_EQ(l1.clause(), l2.clause())
  auto premise = l1.clause();

  /////////////////////////////////////////////////////////////////////////////////////
  // applicability checks
  //////////////////////////////////////////////////////

#if FACTOR_NEGATIVE
  CHECK_CONDITION("sign(j) == sign(k)", j.sign() == k.sign())
  ASS(j.sign() != Sign::Zero)
#else 
  ASS(j.isPositive())
  ASS(k.isPositive())
#endif

  auto s1σ = sigma(s1);
  Stack<TermList> t1σ;
  CHECK_CONDITION("s1σ /⪯ terms(t1)σ",
      l1.contextTerms() 
        .all([&](auto ki_ti) {
          auto tiσ = sigma(ki_ti.atom());
          t1σ.push(NumTraits::mulSimpl(ki_ti.numeral(), tiσ));
          return _shared->notLeq(TermList(s1σ), tiσ);
        }));

  auto s2σ = sigma(s2);
  Stack<TermList> t2σ;
  CHECK_CONDITION("s2σ /⪯ terms(t2)σ",
      l2.contextTerms() 
        .all([&](auto ki_ti) {
          auto tiσ = sigma(ki_ti.atom());
          t2σ.push(NumTraits::mulSimpl(ki_ti.numeral(), tiσ));
          return _shared->notLeq(TermList(s2σ), tiσ);
        }));

                                  //
  Stack<Literal*> concl(premise->size() + cnst->size());

  // adding `Cσ`
  { 
    for (auto i : range(0, premise->size()) ) {
      if (i != l1.litIdx() && i != l2.litIdx()) {
        concl.push(sigma((*premise)[i]));
      }
    }
  }


  // •    (j s1 + t1 >1 0)σ /≺ (k s2 + t2 >2 0 \/ C)σ <- cond1
  //   or (k s2 + t2 >2 0)σ /≺ (j s1 + t1 >1 0 \/ C)σ <- cond2

  auto L1σ = sigma(l1.literal()); // <- (j s1 + t1 >1 0)σ
  auto L2σ = sigma(l2.literal()); // <- (j s1 + t1 >1 0)σ
  auto cond1 = concatIters(concl.iterCloned(), iterItems(L2σ))
    .all([&](auto Lσ) 
        { return  _shared->notLess(L1σ, Lσ); });

  auto cond2 = concatIters(concl.iterCloned(), iterItems(L1σ))
    .all([&](auto Lσ) 
        { return  _shared->notLess(L2σ, Lσ); });

  CHECK_CONDITION(
      "(j s1 + t1 >1 0)σ /≺ (k s2 + t2 >2 0 \\/ C)σ or (k s2 + t2 >2 0)σ /≺ (j s1 + t1 >1 0 \\/ C)σ",
      cond1 || cond2);

  // adding `Cnst`
  concl.loadFromIterator(cnst->iterFifo());

  // adding `(±ks2 + t2 <> 0) σ`
  concl.push(L2σ);

  auto pivotSum = 
  //   ^^^^^^^^--> `(k t1 − j t2)σ`
    NumTraits::sum(concatIters(
          l1.contextTerms().map([&](auto t) { return  sigma(( k * t).toTerm()); }),
          l2.contextTerms().map([&](auto t) { return  sigma((-j * t).toTerm()); })));
    

  // • (>3) = if (>1, >2) = (>=, >) then (>=) 
  //                                else (>)
  auto less3 = l1.symbol() == AlascaPredicate::GREATER_EQ 
            && l2.symbol() == AlascaPredicate::GREATER ? AlascaPredicate::GREATER_EQ
                                                      : AlascaPredicate::GREATER;

  auto pivotLit = createLiteral<NumTraits>(less3, pivotSum);

  // adding (k t1 − j t2 >3 0)σ
  concl.push(pivotLit);

  Inference inf(GeneratingInference1(Kernel::InferenceRule::ALASCA_LITERAL_FACTORING, premise));
  auto out = Clause::fromStack(concl, inf);
  DEBUG("conclusion: ", *out)
  return Option<Clause*>(out);
}

Option<Clause*> InequalityFactoring::applyRule(SelectedAtomicTermItpAny const& l1, SelectedAtomicTermItpAny const& l2)
{
  return l1.apply([&](auto& l1) {
    ASS_EQ(l1.clause(), l2.clause())
    return applyRule(l1, l2.template unwrap<std::remove_const_t<std::remove_reference_t<decltype(l1)>>>());
  });
}

ClauseIterator InequalityFactoring::generateClauses(Clause* premise) 
{
  TIME_TRACE("alasca inequality factoring generate")
  DEBUG("in: ", *premise)

    auto selected = Lib::make_shared(
        _shared->selectedSummands(premise, 
  // TODO think about this, we don't want any literals but one of the two hast to be weakly maximal
                       /* literal */ SelectionCriterion::ANY,
                       /* summand */ SelectionCriterion::NOT_LEQ,
                       /* include number vars */ false)
          .filter([](auto& s) { return s.apply([](auto& s) { return 
              s.isInequality()
#if !FACTOR_NEGATIVE
              && s.numeral().sign() == Sign::Pos
#endif
              ; 
              }); })
          .template collect<Stack>());


  return pvi(range(0, selected->size())
      .flatMap([=](auto i) {
        return range(i + 1, selected->size())
          .filter([=](auto j) { return (*selected)[i].litIdx() != (*selected)[j].litIdx(); })
          .filter([=](auto j) { return (*selected)[i].numTraits() == (*selected)[j].numTraits(); })
          .flatMap([=](auto j) {
              auto& max = (*selected)[i];
              auto& other = (*selected)[j];
              return ifElseIter2(

                  // both literals are the same. 
                  // we use a symmetry breaking index comparison
                  // TODO we could replace this == by _shared.equivalent
                  max.literal() == other.literal() && other.litIdx() < max.litIdx(), 
                  iterItems<Clause*>(),

                  applyRule(other, max).intoIter()
                  ); 
                  
          });
      }));
}

  

#if VDEBUG
void InequalityFactoring::setTestIndices(Stack<Indexing::Index*> const&) { }
#endif

} // namespace ALASCA 
} // namespace Inferences 

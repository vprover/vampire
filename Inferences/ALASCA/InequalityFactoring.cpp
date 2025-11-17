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
    SelectedSummand const& l1,  // +j s1 + t1 >1 0
    SelectedSummand const& l2   // +k s2 + t2 >2 0
    )
{
  using Numeral = typename NumTraits::ConstantType;
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
  auto j = l1.numeral().unwrap<Numeral>();
  auto k = l2.numeral().unwrap<Numeral>();
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

  auto s1_sigma = sigma(s1);
  Stack<TermList> t1_sigma;
  CHECK_CONDITION("s1σ /⪯ terms(t1)σ",
      l1.contextTerms<NumTraits>() 
        .all([&](auto ki_ti) {
          auto tiσ = sigma(ki_ti.factors->denormalize());
          t1_sigma.push(NumTraits::mulSimpl(ki_ti.numeral, tiσ));
          return _shared->notLeq(s1_sigma, tiσ);
        }));

  auto s2_sigma = sigma(s2);
  Stack<TermList> t2_sigma;
  CHECK_CONDITION("s2σ /⪯ terms(t2)σ",
      l2.contextTerms<NumTraits>() 
        .all([&](auto ki_ti) {
          auto tiσ = sigma(ki_ti.factors->denormalize());
          t2_sigma.push(NumTraits::mulSimpl(ki_ti.numeral, tiσ));
          return _shared->notLeq(s2_sigma, tiσ);
        }));

                                  //
  Stack<Literal*> concl(premise->size() + cnst->size());

  // adding `Cσ`
  { 
    for (auto i : range(0, premise->size()) ) {
      if (i != l1.litIdx && i != l2.litIdx) {
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
          l1.contextTerms<NumTraits>().map([&](auto t) { return  sigma(( k * t).denormalize()); }),
          l2.contextTerms<NumTraits>().map([&](auto t) { return  sigma((-j * t).denormalize()); })));
    

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

Option<Clause*> InequalityFactoring::applyRule(SelectedSummand const& l1, SelectedSummand const& l2)
{
  ASS_EQ(l1.clause(), l2.clause())
  return l1.numTraits().apply([&](auto numTraits) {
      return applyRule<decltype(numTraits)>(l1, l2);
  });
}

ClauseIterator InequalityFactoring::generateClauses(Clause* premise) 
{
  TIME_TRACE("alasca inequality factoring generate")
  DEBUG("in: ", *premise)

    auto selected = Lib::make_shared(
        _shared->selectedSummands(premise, 
                       /* literal */ SelectionCriterion::NOT_LESS, 
                       /* summand */ SelectionCriterion::NOT_LEQ,
                       /* include number vars */ false)
          .filter([](auto& s) { return s.isInequality(); })
#if FACTOR_NEGATIVE
          .filter([](auto& s) { return s.sign() != Sign::Zero; })
#else 
          .filter([](auto& s) { return s.sign() == Sign::Pos; })
#endif
          .template collect<Stack>());

  auto rest = Lib::make_shared(
      _shared->selectedSummands(premise,  
                    /* literal */ SelectionCriterion::ANY, 
                    /* summand */ SelectionCriterion::NOT_LEQ,
                    /* include number vars */ false)
        .filter([](auto& s) { return s.isInequality(); })
#if FACTOR_NEGATIVE
        .filter([](auto& s) { return s.sign() != Sign::Zero; })
#else 
        .filter([](auto& s) { return s.sign() == Sign::Pos; })
#endif
        .template collect<Stack>());

  auto selIdx = Lib::make_shared(Set<std::pair<unsigned, unsigned>>());
  auto key = [&](auto& s) { return std::make_pair(s.litIdx, s.termIdx()); };

  DEBUG("selected summands:")
  for (auto& s : *selected) {
    selIdx->insert(key(s));
    DEBUG("  ", s)
  }

  return pvi(range(0, selected->size())
      .flatMap([=](auto i) {
        return range(0, rest->size())
          .filter([=](auto j) { return (*selected)[i].litIdx != (*rest)[j].litIdx; })
          .filter([=](auto j) { return (*selected)[i].numTraits() == (*rest)[j].numTraits(); })
          .flatMap([=](auto j) {
              auto& max = (*selected)[i];
              auto& other = (*rest)[j];
              return ifElseIter3(

                  // both literals are the same. 
                  // we use a symmetry breaking index comparison
                  // TODO we could replace this == by _shared.equivalent
                  max.literal() == other.literal() && other.litIdx < max.litIdx, 
                  arrayIter(Stack<Clause*>{}),

                  // both are selected (= maximal)
                  // we skip one of the application to avoid duplicate results
                  selIdx->contains(key(other)),
                  applyRule(other, max).intoIter(),

                  // only one is selected (= maximal)
                  concatIters(applyRule(max,other).intoIter(), 
                    applyRule(other, max).intoIter())
                  ); 

          });
      }));
}

  

#if VDEBUG
void InequalityFactoring::setTestIndices(Stack<Indexing::Index*> const&) { }
#endif

} // namespace ALASCA 
} // namespace Inferences 

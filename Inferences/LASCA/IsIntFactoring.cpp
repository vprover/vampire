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
 * @file IsIntFactoring.cpp
 * Defines class IsIntFactoring
 *
 */

#include "IsIntFactoring.hpp"
#include "Debug/Assertion.hpp"
#include "Shell/Statistics.hpp"
#include "Debug/TimeProfiling.hpp"

#define DEBUG(...) // DBG(__VA_ARGS__)

namespace Inferences {
namespace LASCA {

void IsIntFactoring::attach(SaturationAlgorithm* salg) { }

void IsIntFactoring::detach() { }


#define CHECK_CONDITION(name, condition)                                                            \
  if (!(condition)) {                                                                               \
    DEBUG("side condition not satisfied: " name)                                                    \
    return nothing();                                                                               \
  }                                                                                                 \

template<class NumTraits>
Option<Clause*> IsIntFactoring::applyRule(NumTraits,
    SelectedSummand const& l1,
    SelectedSummand const& l2 
    )
{
  using Numeral = typename NumTraits::ConstantType;
  TIME_TRACE("lasca inequality factoring application")
  DEBUG("l1: ", l1)
  DEBUG("l2: ", l2)
  ASS_EQ(l1.clause(), l2.clause())
  ASS_EQ(l1.symbol(), Kernel::LascaPredicate::IS_INT_POS)
  ASS_EQ(l2.symbol(), Kernel::LascaPredicate::IS_INT_POS)

  auto nothing = [&]() { return Option<Clause*>{}; };

  auto j = l1.numeral().unwrap<Numeral>();
  auto k = l2.numeral().unwrap<Numeral>();

  CHECK_CONDITION(
      "k / j ∈ Z",
      (k / j).isInt())

  CHECK_CONDITION(
      "symmetry breaking",
      (!(j / k).isInt() || l1 < l2))


  auto uwa_ = _shared->unify(l1.monom(), l2.monom());

  CHECK_CONDITION("⟨σ,Cnst⟩ = uwa(s1,s2)",
                  uwa_.isSome())
  auto& uwa = uwa_.unwrap();

  auto sigma = [&](auto x){ return uwa.subs().apply(x, /* varbank */ 0); };
  auto cnst  = uwa.computeConstraintLiterals();
  auto s1 = l1.monom();
  auto s2 = l2.monom();
  auto premise = l1.clause();

  /////////////////////////////////////////////////////////////////////////////////////
  // applicability checks
  //////////////////////////////////////////////////////


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


  // •    isInt(j s1 + t1)σ /≺ (isInt(k s2 + t2) \/ C)σ <- cond1
  //   or isInt(k s2 + t2)σ /≺ (isInt(j s1 + t1) \/ C)σ <- cond2

  auto L1σ = sigma(l1.literal()); // <- isInt(j s1 + t1)σ
  auto L2σ = sigma(l2.literal()); // <- isInt(k s2 + t2)σ
  auto cond1 = concatIters(concl.iterCloned(), getSingletonIterator(L2σ))
    .all([&](auto Lσ) 
        { return  _shared->notLess(L1σ, Lσ); });

  auto cond2 = concatIters(concl.iterCloned(), getSingletonIterator(L1σ))
    .all([&](auto Lσ) 
        { return  _shared->notLess(L2σ, Lσ); });

  CHECK_CONDITION(
      "isInt(j s1 + t1)σ /≺ (isInt(k s2 + t2) \\/ C)σ or isInt(k s2 + t2)σ /≺ (isInt(j s1 + t1) \\/ C)σ",
      cond1 || cond2);

  // adding `Cnst`
  concl.loadFromIterator(cnst->iterFifo());

  // adding `isInt(js1 + t1) σ`
  concl.push(L1σ);

  auto pivotSum = 
  //   ^^^^^^^^--> `(t2 - (k/j) t1)σ`
    NumTraits::sum(concatIters(
          l2.contextTerms<NumTraits>().map([&](auto t) { return  sigma(            t .denormalize()); }),
          l1.contextTerms<NumTraits>().map([&](auto t) { return  sigma((-(k / j) * t).denormalize()); })));
    

  // adding `~isInt(t2 - (k/j) t1)σ`
  concl.push(NumTraits::isInt(false, pivotSum));

  Inference inf(GeneratingInference1(Kernel::InferenceRule::LASCA_LITERAL_FACTORING, premise));
  auto out = Clause::fromStack(concl, inf);
  DEBUG("conclusion: ", *out)
  return Option<Clause*>(out);
}

Option<Clause*> IsIntFactoring::applyRule(SelectedSummand const& l1, SelectedSummand const& l2)
{
  ASS_EQ(l1.clause(), l2.clause())
  return l1.numTraits().apply([&](auto numTraits) {
      return applyRule(numTraits, l1, l2);
  });
}

ClauseIterator IsIntFactoring::generateClauses(Clause* premise) 
{
  TIME_TRACE("lasca inequality factoring generate")
  DEBUG("in: ", *premise)

    auto selected = make_shared(
        _shared->selectedSummands(premise, 
                       /* literal */ SelectionCriterion::NOT_LESS, 
                       /* summand */ SelectionCriterion::NOT_LEQ,
                       /* include number vars */ false)
          .filter([](auto& s) { return s.symbol() == LascaPredicate::IS_INT_POS; })
          .filter([](auto& s) { return s.sign() != Sign::Zero; })
          .template collect<Stack>());

  auto rest = make_shared(
      _shared->selectedSummands(premise,  
                    /* literal */ SelectionCriterion::ANY, 
                    /* summand */ SelectionCriterion::NOT_LEQ,
                    /* include number vars */ false)
        .filter([](auto& s) { return s.symbol() == LascaPredicate::IS_INT_POS; })
        .filter([](auto& s) { return s.sign() != Sign::Zero; })
        .template collect<Stack>());

  auto selIdx = make_shared(Set<std::pair<unsigned, unsigned>>());
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
                  // we skip one of the applicaiton to avoid duplicate results
                  selIdx->contains(key(other)), 
                  applyRule(other, max).intoIter(),

                  // only one is selected (= maximal)
                  concatIters(applyRule(max,other).intoIter(), 
                              applyRule(other, max).intoIter()) );
          });
      }));
}

  

#if VDEBUG
void IsIntFactoring::setTestIndices(Stack<Indexing::Index*> const&) { }
#endif

} // namespace LASCA 
} // namespace Inferences 

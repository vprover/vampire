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
 * @file TermFactoring.cpp
 * Implements class TermFactoring.
 */

#include "Lib/STL.hpp"

#include "Lib/Metaiterators.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Debug/TimeProfiling.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "TermFactoring.hpp"
#include "Kernel/RobSubstitution.hpp"

#define DEBUG(...) // DBG(__VA_ARGS__)


namespace Inferences {
namespace ALASCA {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

void TermFactoring::attach(SaturationAlgorithm* salg)
{
  GeneratingInferenceEngine::attach(salg);
}

void TermFactoring::detach()
{
  ASS(_salg);
  GeneratingInferenceEngine::detach();
}


//   C ∨ k₁ s₁ + k₂ s₂  + t <> 0
// ---------------------------------------
// ( C ∨  (k₁ + k₂) s₁ + t <> 0 )σ ∨ Cnst
//
// where 
// • (σ, Cnst) = uwa(s₁, s₂)
// • <> ∈ {>,≥,≈,/≈}
// • s₁,s₂ /∈ Vars
// • (k₁ s₁ + k₂ s₂ + t <> 0)σ /≺ Cσ
// • s₁σ,s₂σ ∈ maxAtoms((C ∨ k₁ s₁ + k₂ s₂  + t <> 0)σ)
template<class NumTraits> 
Option<Clause*> TermFactoring::applyRule(
    SelectedSummand const& sel1, 
    SelectedSummand const& sel2,
    Stack<TermList> const& maxAtoms
    )
{
  TIME_TRACE("alasca term factoring")
  using Numeral = typename NumTraits::ConstantType;
  DEBUG("L1: ", sel1)
  DEBUG("L2: ", sel2)


#define check_side_condition(cond, cond_code)                                                       \
    if (!(cond_code)) {                                                                             \
      DEBUG("side condition not fulfilled: " cond)                                                  \
      return nothing();                                                                             \
    }                                                                                               \

  auto nothing = [&]() { return Option<Clause*>(); };

  // ASS(!(sel1.literal()->isEquality() && sel1.literal()->isNegative()))

  auto k1 = sel1.numeral().template unwrap<Numeral>();
  auto k2 = sel2.numeral().template unwrap<Numeral>();
  auto s1 = sel1.selectedAtom();
  auto s2 = sel2.selectedAtom();

  check_side_condition(
      "s₁, s₂ are not variables",
      !s1.isVar() && !s2.isVar())

  auto uwa = _shared->unify(s1, s2);
  if (uwa.isNone())  
    return nothing();

  auto cnst = uwa->computeConstraintLiterals();
  auto sigma = [&](auto t) { return uwa->subs().apply(t, /* var bank */ 0); };

  // auto pivot_sigma = sigma(sel1.literal());
  // //   ^^^^^^^^^^^ (k₁ s₁ + k₂ s₂ + t <> 0)σ

  Stack<Literal*> conclusion(sel1.clause()->size() + cnst->size());

  // adding `Cσ`, and checking side condition
  for (auto l : sel1.contextLiterals()) {
    conclusion.push(sigma(l));
  }

  // • s₁,s₂ /∈ MaxTerms(C ∨ k₁ s₁ + k₂ s₂  + t <> 0)σ

  auto s1_sigma = sigma(s1);
  auto s2_sigma = sigma(s2);
  auto resTerm = NumTraits::mul(NumTraits::constantTl(k1 + k2), s1_sigma); 
  //   ^^^^^^^---> ((k₁ + s₁)s₂)σ



  // • s₁σ,s₂σ ∈ maxAtoms((C ∨ k₁ s₁ + k₂ s₂  + t <> 0)σ)
    check_side_condition(
        "s₁σ,s₂σ ∈ maxAtoms((C ∨ k₁ s₁ + k₂ s₂  + t <> 0)σ)",
        iterTraits(maxAtoms.iterFifo())
          .all([&](auto a) {
            auto a_sigma = sigma(a);
            return _shared->notLess(s1_sigma, a_sigma) 
               &&  _shared->notLess(s2_sigma, a_sigma);
            }))
  //
  // {
  //   auto cmp = _shared->ordering->compare(s1_sigma, s2_sigma);
  //   check_side_condition(
  //       "s₁σ /≺ s₂σ and s₂σ /≺ s₂σ ",
  //       cmp == Ordering::Result::EQUAL || cmp == Ordering::Result::INCOMPARABLE)
  // }
  //
  // Stack<TermList> t_sigma(sel1.nContextTerms());
  //
  // check_side_condition(
  //     "s₁σ /≺ atoms(t)σ and s₂σ /≺ atoms(t)σ ",
  //     range(0, sel1.alascaLiteral<NumTraits>().term().nSummands())
  //         .filter([&](auto i) { return i != sel1.termIdx() && i != sel2.termIdx(); })
  //         .all([&](auto i) {
  //           auto ki_ti = sel1.alascaLiteral<NumTraits>().term().summandAt(i);
  //           auto tiσ = sigma(ki_ti.factors->denormalize());
  //           t_sigma.push(NumTraits::mulSimpl(ki_ti.numeral, tiσ));
  //           return _shared->notLess(s1_sigma, tiσ)
  //               && _shared->notLess(s2_sigma, tiσ);
  //         }))
  //
  // auto resSum = NumTraits::sum(concatIters(iterItems(resTerm), t_sigma.iterFifo()));
  // //   ^^^^^^---> ((k₁ + s₁)s₂ + t)σ
    
  auto t_sigma = range(0, sel1.alascaLiteral<NumTraits>().term().nSummands())
          .filter([&](auto i) { return i != sel1.termIdx() && i != sel2.termIdx(); })
          .map([&](auto i) {
            auto ki_ti = sel1.alascaLiteral<NumTraits>().term().summandAt(i);
            auto tiσ = sigma(ki_ti.factors->denormalize());
            return NumTraits::mulSimpl(ki_ti.numeral, tiσ);
          });

  auto resSum = NumTraits::sum(concatIters(iterItems(resTerm), t_sigma));
  //   ^^^^^^---> ((k₁ + s₁)s₂ + t)σ
    
  auto resLit = createLiteral<NumTraits>(sel1.symbol(), resSum);
  //   ^^^^^^---> ((k₁ + s₁)s₂ + t <> 0)σ


  // adding `((k₁ + k₂)s₁ + t <> 0)σ`
  conclusion.push(resLit);

  // adding `Cnst`
  conclusion.loadFromIterator(cnst->iterFifo());

  Inference inf(GeneratingInference1(Kernel::InferenceRule::ALASCA_TERM_FACTORING, sel1.clause()));
  auto clause = Clause::fromStack(conclusion, inf);
  DEBUG("result: ", *clause);
  return Option<Clause*>(clause);
}

Option<Clause*> TermFactoring::applyRule(
    SelectedSummand const& l, 
    SelectedSummand const& r,
    Stack<TermList> const& maxAtoms
    )
{ 
  ASS_EQ(l.clause(), r.clause())
  ASS_EQ(l.literal(), r.literal())
  return l.numTraits().apply([&](auto numTraits) 
      { return applyRule<decltype(numTraits)>(l, r, maxAtoms); });
}

#define D(...) std::cout  << __VA_ARGS__ << std::endl;

ClauseIterator TermFactoring::generateClauses(Clause* premise)
{
  TIME_TRACE("alasca term factoring generate")
  DEBUG("in: ", *premise)

  auto max = Lib::make_shared(Stack<TermList>());
  auto selected = Lib::make_shared(
        _shared->maxAtoms(premise,
          SelectionCriterion::NOT_LESS,
          /* include number vars */ false)
        .inspect([&](auto& sel) { max->push(sel.atom()); })
        .filterMap([](auto x) -> Option<SelectedSummand> { return x.template as<SelectedSummand>().toOwned(); })
        .template collect<Stack>());

  max->sort();
  max->dedup();

  std::sort(selected->begin(), selected->end(), [](auto& l, auto& r) { return l.literal() < r.literal(); });

#if __DEBUG_OUTPUT
  DEBUG("selected summands:")
  for (auto& s : *selected) {
    DEBUG("  ", s)
  }
#endif

  Stack<std::pair<unsigned, unsigned>> litRanges;
  unsigned last = 0;
  for (unsigned i = 1; i < selected->size(); i++) {
    if ((*selected)[last].literal() != (*selected)[i].literal()) {
      litRanges.push(std::make_pair(last, i));
      last = i;
    }
  }
  if (selected->size() > 0)
    litRanges.push(std::make_pair(last, selected->size()));

  return pvi(arrayIter(std::move(litRanges))
                .flatMap([=] (auto r) {
                       ASS(r.first < r.second)
                       return range(r.first, r.second - 1)
                                .flatMap([=](auto i) {
                                   return range(i + 1, r.second)
                                            .filterMap([=](auto j) 
                                              { return applyRule((*selected)[i], (*selected)[j], *max); });
                        });
                     }));
}

} // namespace ALASCA
} // namespace Inferences

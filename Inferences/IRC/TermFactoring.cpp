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

#include "Debug/RuntimeStatistics.hpp"
#include "Lib/STL.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/PairUtils.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/ColorHelper.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/LiteralSelector.hpp"
#include "Kernel/SortHelper.hpp"
#include "Lib/TypeList.hpp"
#include "Shell/Statistics.hpp"

#include "Indexing/Index.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "TermFactoring.hpp"
#include "InequalityResolution.hpp"
#include "Kernel/PolynomialNormalizer.hpp"
#include "Kernel/IRC.hpp"
#include "Indexing/TermIndexingStructure.hpp"
#include "Kernel/RobSubstitution.hpp"

#define DEBUG(...)  //DBG(__VA_ARGS__)

using Kernel::InequalityLiteral;

namespace Inferences {
namespace IRC {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

void TermFactoring::attach(SaturationAlgorithm* salg)
{
  CALL("TermFactoring::attach");
  GeneratingInferenceEngine::attach(salg);
}

void TermFactoring::detach()
{
  CALL("TermFactoring::detach");
  ASS(_salg);
  GeneratingInferenceEngine::detach();
}



#if VDEBUG
void TermFactoring::setTestIndices(Stack<Indexing::Index*> const& indices)
{  }
#endif

#define OVERFLOW_SAFE 1

#define ASSERT_NO_OVERFLOW(...)                                                                     \
  [&]() { try { return __VA_ARGS__; }                                                               \
          catch (MachineArithmeticException&) { ASSERTION_VIOLATION } }()                           \

auto rng(unsigned from, unsigned to)
{ return iterTraits(getRangeIterator(from,to)); }

//   C ∨  k1 s1 + k2 s2  + t <> 0
// ---------------------------------------
// ( C ∨    (k1 + k2)s1 + t <> 0 )σ ∨ Cnst
//
// where 
// - (σ, Cnst) = uwa(s1, s2)
// - <> ∈ {>,≥,≈}
// - s,s /∈ Vars
// - (k1 s1 + k2 s2 + t <> 0)σ /≺ Cσ
// - s1σ /≺ terms(s2 + t)σ
// - s2σ /≺ terms(s1 + t)σ
// - k1 or k2 is positive
template<class NumTraits> 
Option<Clause*> TermFactoring::applyRule(
    SelectedSummand const& sel1, SelectedSummand const& sel2)
{
  MeasureTime time(env.statistics->ircTermFac);
  using Numeral = typename NumTraits::ConstantType;
  DEBUG("L1: ", sel1)
  DEBUG("L2: ", sel2)


#define check_side_condition(cond, cond_code)                                                       \
    if (!(cond_code)) {                                                                             \
      DEBUG("side condition not fulfiled: " cond)                                                   \
      return nothing();                                                                             \
    }                                                                                               \

  auto nothing = [&]() { time.applicationCancelled(); return Option<Clause*>(); };
  auto createLiteral = [&](auto term, auto sym) -> Literal* {
      switch(sym) {
        case IrcPredicate::EQ:         return NumTraits::eq(true,  term, NumTraits::zero());
        case IrcPredicate::NEQ:        return NumTraits::eq(false, term, NumTraits::zero());
        case IrcPredicate::GREATER:    return NumTraits::greater(true, term, NumTraits::zero());
        case IrcPredicate::GREATER_EQ: return NumTraits::geq    (true, term, NumTraits::zero());
      }
      ASSERTION_VIOLATION
    };

  // ASS(!(sel1.literal()->isEquality() && sel1.literal()->isNegative()))

  auto k1 = sel1.numeral().template unwrap<Numeral>();
  auto k2 = sel2.numeral().template unwrap<Numeral>();
  auto s1 = sel1.monom();
  auto s2 = sel2.monom();

  check_side_condition(
      "k1 or k2 is positive ",
      (sel1.sign() == Sign::Pos || sel2.sign() == Sign::Pos || sel1.literal()->isEquality()))

  check_side_condition(
      "s1, s2 are not variables",
      !sel1.monom().isVar() && !sel2.monom().isVar())

  auto uwa_ = _shared->unify(s1, s2);
  if (uwa_.isNone())  
    return nothing();

  auto& uwa = uwa_.unwrap();
  auto sigma = [&](auto t) { return uwa.sigma(t, /* var bank */ 0); };

  auto pivot_sigma = sigma(sel1.literal());
  //   ^^^^^^^^^^^ (k1 s1 + k2 s2 + t <> 0)σ

  Stack<Literal*> conclusion(sel1.clause()->size() + uwa.cnst().size());

  // adding `Cσ`, and checking side condition
  check_side_condition(
      "(k1 s1 + k2 s2 + t <> 0)σ /≺ Cσ",
      sel1.contextLiterals()
          .all([&](auto l) {
            auto lσ = sigma(l);
            conclusion.push(lσ);
            return _shared->notLess(pivot_sigma, lσ);
          }))

  auto s1_sigma = sigma(s1);
  auto s2_sigma = sigma(s2);
  auto resTerm = NumTraits::mul(NumTraits::constantTl(k1 + k2), s1_sigma); 
  //   ^^^^^^^---> ((k1 + s1)s2)σ


  {
    auto cmp = _shared->ordering->compare(s1_sigma, s2_sigma);
    check_side_condition(
        "s1σ /≺ s2σ and s2σ /≺ s2σ ",
        cmp == Ordering::Result::EQUAL || cmp == Ordering::Result::INCOMPARABLE)
  }

  Stack<TermList> t_sigma(sel1.nContextTerms());

  check_side_condition(
      "s1σ /≺ atoms(t)σ and s2σ /≺ atoms(t)σ ",
      range(0, sel1.ircLiteral<NumTraits>().term().nSummands())
          .filter([&](auto i) { return i != sel1.termIdx() && i != sel2.termIdx(); })
          .all([&](auto i) {
            auto ki_ti = sel1.ircLiteral<NumTraits>().term().summandAt(i);
            auto tiσ = sigma(ki_ti.factors->denormalize());
            t_sigma.push(NumTraits::mulSimpl(ki_ti.numeral, tiσ));
            return _shared->notLess(s1_sigma, tiσ)
                && _shared->notLess(s2_sigma, tiσ);
          }))

  auto resSum = NumTraits::sum(concatIters(getSingletonIterator(resTerm), t_sigma.iterFifo()));
  //   ^^^^^^---> ((k1 + s1)s2 + t)σ
    
  auto resLit = createLiteral(resSum, sel1.symbol());
  //   ^^^^^^---> ((k1 + s1)s2 + t <> 0)σ


  // adding `((k1 + k2)s1 + t <> 0)σ`
  conclusion.push(resLit);

  // adding `Cnst`
  conclusion.loadFromIterator(uwa.cnstLiterals());

  Inference inf(GeneratingInference1(Kernel::InferenceRule::IRC_TERM_FACTORING, sel1.clause()));
  auto clause = Clause::fromStack(conclusion, inf);
  DEBUG("result: ", *clause);
  return Option<Clause*>(clause);
}

Option<Clause*> TermFactoring::applyRule(SelectedSummand const& l, SelectedSummand const& r)
{ 
  ASS_EQ(l.clause(), r.clause())
  ASS_EQ(l.literal(), r.literal())
  return l.numTraits().apply([&](auto numTraits) 
      { return applyRule<decltype(numTraits)>(l, r); });
}

ClauseIterator TermFactoring::generateClauses(Clause* premise)
{
  CALL("TermFactoring::generateClauses");
  DEBUG("in: ", *premise)

  auto selected = make_shared(move_to_heap(
        _shared->selectedSummands(premise, /* literal */ SelectionCriterion::WEAKLY_MAX, /* summand */ SelectionCriterion::WEAKLY_MAX)
        .filter([](auto& s) { return !s.monom().isVar(); })
        .template collect<Stack>()));

  std::sort(selected->begin(), selected->end(), [](auto& l, auto& r) { return l.literal() < r.literal(); });

  DEBUG("selected summands:")
  for (auto& s : *selected) {
    DEBUG("  ", s)
  }

  Stack<pair<unsigned, unsigned>> litRanges;
  unsigned last = 0;
  for (unsigned i = 1; i < selected->size(); i++) {
    if ((*selected)[last].literal() != (*selected)[i].literal()) {
      litRanges.push(make_pair(last, i));
      last = i;
    }
  }
  if (selected->size() > 0)
    litRanges.push(make_pair(last, selected->size()));

  return pvi(iterTraits(ownedArrayishIterator(std::move(litRanges)))
                .flatMap([this, selected = std::move(selected)] (auto r) {
                       ASS_REP(r.first < r.second, r)
                       return range(r.first, r.second - 1)
                                .flatMap([=](auto i) {
                                   return range(i + 1, r.second)
                                            .filterMap([=](auto j) 
                                              { return applyRule((*selected)[i], (*selected)[j]); });
                        });
                     }));
}

} // namespace IRC
} // namespace Inferences

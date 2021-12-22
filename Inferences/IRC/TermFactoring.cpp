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

#define DEBUG(...)  // DBG(__VA_ARGS__)

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

#define ASSERT_NO_OVERFLOW(...)                                                                               \
  [&]() { try { return __VA_ARGS__; }                                                                         \
          catch (MachineArithmeticException&) { ASSERTION_VIOLATION } }()                                     \

auto rng(unsigned from, unsigned to)
{ return iterTraits(getRangeIterator(from,to)); }

//   C ∨  k1 s1 + k2 s2  + t <> 0
// ---------------------------------------
// ( C ∨    (k1 + k2)s1 + t <> 0 )σ ∨ Cnst
//
// where 
// - (σ, Cnst) = uwa(s1, s2)
// - <> ∈ {>,≥,≈,/≈}
// - s,s /∈ Vars
// - (k1 s1 + k2 s2 + t <> 0)σ /≺ Cσ
// - s1σ /≺ terms(s2 + t)σ
// - s2σ /≺ terms(s1 + t)σ
template<class NumTraits> Option<Clause*> TermFactoring::applyRule(
    Clause* premise,
    Literal* lit,
    IrcLiteral<NumTraits> pivot,
    Monom<NumTraits> k1_s1,
    Monom<NumTraits> k2_s2)
{
  auto nothing = []() { return Option<Clause*>(); };
  auto createLiteral = [&](auto term, auto sym) -> Literal* {
      switch(sym) {
        case IrcPredicate::EQ:         return NumTraits::eq(true,  term, NumTraits::zero());
        case IrcPredicate::NEQ:        return NumTraits::eq(false, term, NumTraits::zero());
        case IrcPredicate::GREATER:    return NumTraits::greater(true, term, NumTraits::zero());
        case IrcPredicate::GREATER_EQ: return NumTraits::geq    (true, term, NumTraits::zero());
      }
      ASSERTION_VIOLATION
    };
  auto k1 = k1_s1.numeral;
  auto k2 = k2_s2.numeral;
  auto s1 = k1_s1.factors->denormalize();
  auto s2 = k2_s2.factors->denormalize();

  auto uwa_ = _shared->unify(s1, s2);
  if (uwa_.isNone()) 
    return nothing();

  auto& uwa = uwa_.unwrap();
  auto sigma = [&](auto t) { return uwa.sigma.apply(t, /* var bank */ 0); };

  auto s1_sigma = sigma(s1);
  auto resTerm = NumTraits::mul(NumTraits::constantTl(k1 + k2), s1_sigma); //sigma(Monom<NumTraits>(k1 + k2, s1).denormalize();)
  //   ^^^^^^^---> ((k1 + s1)s2)σ

  auto cntFound = 0;
  auto t_sigma 
  //   ^^^^^^^---> tσ
    = pivot.term().iterSummands()
                  .filter([&](auto x) { 
                      auto found = x == k1_s1 || x == k2_s2; 
                      if (found) cntFound++;
                      return !found;
                  })
                  .map([&](auto x) { return sigma(x.denormalize()); })
                  .template collect<Stack>();
  ASS_EQ(cntFound, 2)

  auto resSum = NumTraits::sum(getConcatenatedIterator(getSingletonIterator(resTerm),t_sigma.iterFifo()));
  //   ^^^^^^---> ((k1 + s1)s2 + t)σ
    
  auto resLit = createLiteral(resSum, pivot.symbol());
  //   ^^^^^^---> ((k1 + s1)s2 + t <> 0)σ

  Stack<Literal*> conclusion(premise->size() + uwa.cnst.size());

  // adding `Cσ`
  {
    auto litFound = 0;
    for (auto l : iterTraits(premise->getLiteralIterator())) {
      if (l == lit) {
        litFound++;
      } else {
        conclusion.push(sigma(l));
      }
    }
    ASS_EQ(litFound, 1)
  }

  // checking (k1 s1 + k2 s2 + t <> 0) /≺ Cσ
  {
    auto pivot_sigma = sigma(lit);
    if (iterTraits(conclusion.iterFifo())
         .any([&](auto l) { return _shared->ordering->compare(pivot_sigma, l) == Ordering::LESS; }))
      return nothing();
  }

  // adding `((k1 + k2)s1 + t <> 0)σ`
  conclusion.push(resLit);

  // checking s1σ /≺ terms(s2 + t)σ
  // checking s2σ /≺ terms(s1 + t)σ
  { 
    auto s2_sigma = sigma(s2);
    auto cmp = _shared->ordering->compare(s1_sigma, s2_sigma);
    if (cmp == Ordering::LESS || cmp == Ordering::GREATER)
      return nothing();

    if (iterTraits(t_sigma.iterFifo()).any([&](auto t) 
          { return _shared->ordering->compare(s1_sigma, t) == Ordering::LESS 
                || _shared->ordering->compare(s2_sigma, t) == Ordering::LESS; }))
      return nothing();
  }

  // adding `Cnst`
  conclusion.loadFromIterator(uwa.cnstLiterals());

  env.statistics->ircTermFacCnt++;

  Inference inf(GeneratingInference1(Kernel::InferenceRule::IRC_TERM_FACTORING, premise));
  return Option<Clause*>(Clause::fromStack(conclusion, inf));
}

template<class NumTraits> ClauseIterator TermFactoring::generateClauses(Clause* premise, Literal* lit, IrcLiteral<NumTraits> L)
{
  auto selected = make_shared(new Stack<Monom<NumTraits>>(_shared->maxAtomicTerms(L)));

  return pvi( rng(0, selected->size())
      .flatMap([=](auto i) {
        return pvi( rng(i + 1, selected->size())
            .filterMap([=](auto j) {
              auto k1_s1 = (*selected)[i];
              auto k2_s2 = (*selected)[j];
              return applyRule(premise, lit, L, k1_s1, k2_s2);
            }));
        }));
}

ClauseIterator TermFactoring::generateClauses(Clause* premise)
{
  CALL("TermFactoring::generateClauses");
  DEBUG("in: ", *premise)
  auto selected = _shared->maxLiterals(premise, /* strict = */ false);
  return pvi(iterTraits(ownedArrayishIterator(std::move(selected)))
          .flatMap([=](auto lit) 
            { return pvi(iterTraits(_shared->normalize(lit).intoIter())
                        .flatMap([&](AnyIrcLiteral polymorphic) -> ClauseIterator
                          { return polymorphic
                                      .apply([&](auto L)  -> ClauseIterator
                                         { return generateClauses(premise, lit, L); }); })); 
            }));
}

} // namespace IRC
} // namespace Inferences

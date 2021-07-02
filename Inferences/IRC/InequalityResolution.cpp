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
 * @file InequalityResolution.cpp
 * Implements class InequalityResolution.
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


#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "InequalityResolution.hpp"
#include "Shell/UnificationWithAbstractionConfig.hpp"
#include "Kernel/PolynomialNormalizer.hpp"
#include "Kernel/IRC.hpp"
#include "Indexing/TermIndexingStructure.hpp"

#define DEBUG(...) // DBG(__VA_ARGS__)

using Kernel::InequalityLiteral;

namespace Inferences {
namespace IRC {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

void InequalityResolution::attach(SaturationAlgorithm* salg)
{
  CALL("InequalityResolution::attach");
  ASS(!_index);

  GeneratingInferenceEngine::attach(salg);
  _index=static_cast<InequalityResolutionIndex*> (
	  _salg->getIndexManager()->request(IRC_INEQUALITY_RESOLUTION_SUBST_TREE) );
  _index->setShared(_shared);
}

void InequalityResolution::detach()
{
  CALL("InequalityResolution::detach");
  ASS(_salg);

  _index=0;
  _salg->getIndexManager()->release(IRC_INEQUALITY_RESOLUTION_SUBST_TREE);
  GeneratingInferenceEngine::detach();
}



#if VDEBUG
void InequalityResolution::setTestIndices(Stack<Indexing::Index*> const& indices)
{ 
  _index = (InequalityResolutionIndex*) indices[0]; 
  _index->setShared(_shared);
}
#endif



using Lib::TypeList::List;
using Lib::TypeList::Indices;
using Lib::TypeList::UnsignedList;

// template<class F, class... Capt>
// class Capture
// {
//   
//   template<class... Args> using Result = typename std::result_of<F(Capt..., Args...)>::type;
//   F _fun;
//   std::tuple<Capt...> _capt;
// public:
//   Capture(F fun, Capt... capt) : _fun(std::move(fun)), _capt(std::forward<Capt>(capt)...) {}
//
//   template<class... Args>
//   Result<Args...> operator()(Args... args)
//   { return apply(Indices<List<Args...>>{}, std::forward<Args>(args)...); }
//
//   template<class... Args, int... idx>
//   Result<Args...> apply(UnsignedList<idx...>, Args... args)
//   { return _fun(std::get<idx>(_capt)..., std::forward<Args>(args)...); }
// };
//
// template<class F, class... Capt>
// Capture<F, Capt...> capture(F f, Capt... capt) 
// { return Capture<F,Capt...>(std::move(f), capt...); }

// template<class NumTraits> 
// Stack<Monom<NumTraits>> InequalityResolution::maxTerms(InequalityLiteral<NumTraits> const& lit, Ordering* ord) 
// { return maxTerms(lit.inner(), ord); }
//
//
// template<class NumTraits> 
// Stack<Monom<NumTraits>> InequalityResolution::maxTerms(IrcLiteral<NumTraits> const& lit, Ordering* ord) 
// { 
//   using Monom = Monom<NumTraits>;
//   Stack<Monom> max(lit.term().nSummands()); // TODO not sure whether this size allocation brings an advantage
//   auto monoms = lit.term().iterSummands().template collect<Stack>();
//   for (unsigned i = 0; i < monoms.size(); i++) {
//     auto isMax = true;
//     for (unsigned j = 0; j < monoms.size(); j++) {
//       auto cmp = ord->compare(
//           monoms[i].factors->denormalize(), 
//           monoms[j].factors->denormalize());
//       if (cmp == Ordering::LESS) {
//           isMax = false;
//           break;
//       } else if(cmp == Ordering::EQUAL || cmp == Ordering::INCOMPARABLE || Ordering::GREATER) {
//         /* ok */
//       } else {
//         ASSERTION_VIOLATION_REP(cmp)
//       }
//     }
//     if (isMax && monoms[i].factors->tryVar().isNone())  // TODO we don't wanna skip varibles in the future
//       max.push(monoms[i]);
//   }
//   return max;
// }

#define OVERFLOW_SAFE 1

#define ASSERT_NO_OVERFLOW(...)                                                                               \
  [&]() { try { return __VA_ARGS__; }                                                                         \
          catch (MachineArithmeticException&) { ASSERTION_VIOLATION }}()                                      \



template<class NumTraits>
ClauseIterator InequalityResolution::generateClauses(Clause* cl1, Literal* literal1, InequalityLiteral<NumTraits> lit1) const
  //                                                                                         num1 * term + rest1 >= 0 <-- ^^^^
{
  CALL("InequalityResolution::generateClauses(Clause*, Literal*) const")
  using Monom             = Monom<NumTraits>;
  using MonomFactors      = MonomFactors<NumTraits>;
  using Numeral           = typename Monom::Numeral;
  using InequalityLiteral = InequalityLiteral<NumTraits>;
  const bool isInt        = std::is_same<NumTraits, IntTraits>::value;

  // auto lit1Opt = this->normalizer().normalizeIneq<NumTraits>(literal1);
  // if (lit1Opt.isNone()) 
  //   return ClauseIterator::getEmpty();

  // The rule we compute looks as follows for rat & real:
  //
  // num1 * term + rest1 > 0 \/ C1      num2 * term2 + rest2 > 0 \/ C2
  // --------------------------------------------------------------------
  //         k1 * rest1 + k2 * rest2 > 0 \/ C1 \/ C2
  //
  // or in the integer case
  //
  // num1 * term + rest1 > 0 \/ C1      num2 * term2 + rest2 > 0 \/ C2
  // --------------------------------------------------------------------
  //         k1 * rest1 + k2 * rest2 - 1 > 0 \/ C1 \/ C2

  // TODO overflow statistics in IrcState
  // auto lit1_ = std::move(lit1Opt).unwrap();
  // if (lit1_.overflowOccurred) { 
  //   env.statistics->irOverflowNorm++;
  //   return Option<ClauseIterator>();
  // }
  // auto lit1 = lit1_.value;
  //   ^^^^--> num1 * term + rest1 >= 0

  auto maxHyp1 = _shared->maxAtomicTermsNonVar<NumTraits>(cl1);

  DEBUG("lit1: ", lit1)
  return pvi(iterTraits(ownedArrayishIterator(_shared->maxAtomicTerms(lit1.inner())))
    .filter([maxHyp1 = std::move(maxHyp1), literal1](Monom monom) 
      { return iterTraits(maxHyp1.iterFifo()) // TODO use a set instead of iterating over this
                  .find([&](auto x) { return x.self == monom && literal1 == x.literal; })
                  .isSome(); })
    .flatMap([this, cl1, lit1, literal1](Monom monom)  -> VirtualIterator<Clause*> { 
      CALL("InequalityResolution::generateClauses:@clsr1")
      auto num1  = monom.numeral;
      auto term1 = monom.factors;
      DEBUG("monom1: ", monom)


      return pvi(iterTraits(_index->getUnificationsWithConstraints(term1->denormalize(), true))
                .filterMap([this, cl1, lit1, literal1, num1, term1](TermQueryResult res) -> Option<Clause*> {
                    CALL("InequalityResolution::generateClauses:@clsr2")
                    auto& subs = *res.substitution;

                    auto cl2   = res.clause;

                    auto term2 =
                      normalizeTerm(TypedTermList(res.term, NumTraits::sort()))
#if OVERFLOW_SAFE
                        /* the term might also be a polynom if we for example can't multily out 2 * (k + x) 
                          * to 2k + 2x because 2k would overflow */
                        .wrapMonom<NumTraits>() 
#else
                        .downcast<NumTraits>().unwrap()->tryMonom().unwrap()
#endif
                        .factors;
                    auto literal2 = res.literal;
                    auto lit2_ = this->normalizer().normalizeIneq<NumTraits>(literal2).unwrap();
                    ASS(!lit2_.overflowOccurred)
                    auto lit2  = lit2_.value;
                    //   ^^^^ ~=  num2 * term2 + rest2 >= 0
                    auto strictness = lit1.strict() || lit2.strict();
                    //   ^^^^^^^^^^ if either of the two inequalities is strict, the result will be as well.
                    //              consider e.g.
                    //                    s + t > 0 /\ u - t >= 0 
                    //                ==> s + t > 0 /\ 0 >= t - u 
                    //                ==> s + t > t - u 
                    //                ==> s + u > 0

                    auto num2 = lit2.term()
                                    .iterSummands()
                                    .find([&](Monom m) { return m.factors == term2; })
                                    .unwrap()
                                    .numeral;

                    if (num1.isNegative() == num2.isNegative())
                      return Option<Clause*>();

                    DEBUG("  resolving against: ", lit2, " (term: ", term2, ", constr: ", res.constraints, ")");

                    pair<Numeral,Numeral> factors;
                    //                    ^^^^^^^--> (k1, k2)
                    try {
                      factors = computeFactors(num1, num2);
                      ASS_REP(factors.first.isPositive() && factors.second.isPositive(), factors)

                    } catch (MachineArithmeticException&) {
                      return Option<Clause*>();
                    }

                    bool strictlyMaxAfterUnification = true;

                    auto resolventSum = NumTraits::zero();
                    //   ^^^^^^^^^^^^--> gonna be k1 * rest1 + k2 * rest2 

                    try {
                      auto pushTerms = [&](InequalityLiteral lit, Perfect<MonomFactors> termToSkip, Numeral num, bool resultVarBank)
                                {
                                  auto pivot = subs.applyTo(termToSkip->denormalize(), resultVarBank);
                                  auto iter = lit.term()
                                      .iterSummands()
                                      .filter([&](Monom m) { return m.factors != termToSkip; })
                                      .map   ([&](Monom m) { 
                                          auto atomic = subs.applyTo(m.factors->denormalize(),resultVarBank); 
                                          auto cmp = _shared->ordering->compare(pivot, atomic);
                                          strictlyMaxAfterUnification &= cmp != Ordering::EQUAL 
                                                                      && cmp != Ordering::LESS;

                                          auto numeral = NumTraits::constantTl(m.numeral * num);
                                          auto out = NumTraits::mul(numeral, atomic);
                                          return out;
                                      });
                                  for (auto x : iter) {
                                    resolventSum = NumTraits::add(x, resolventSum);
                                  }
                                };

                      pushTerms(lit1, term1, factors.first , false);
                      pushTerms(lit2, term2, factors.second, true);
                      if (isInt) {
                        resolventSum = NumTraits::add(resolventSum, NumTraits::constantTl(-1));
                        // resolventSum.push(Monom(Numeral(-1)));
                      }
                    } catch (MachineArithmeticException&) {
                      return Option<Clause*>();
                    }

                    if (!strictlyMaxAfterUnification)
                      return Option<Clause*>();

                    // auto sum = PolynomialEvaluation::simplifySummation(std::move(resolventSum));
                    auto normResolventSum = normalizeTerm(resolventSum, NumTraits::sort()).template wrapPoly<NumTraits>();
                    auto sum = _shared->normalizer.evaluator().evaluate(normResolventSum).map([&](auto eval) { return eval || normResolventSum; });
                    if (sum.overflowOccurred) {
                      return Option<Clause*>(); 
                    }
                    // auto resolventLit = InequalityLiteral(perfect(sum.value), strictness);
                    auto resolventLit = InequalityLiteral(sum.value, strictness);
                    //   ^^^^^^^^^^^^--> k1 * rest1 + k2 * rest2 >= 0

                    Inference inf(GeneratingInference2(Kernel::InferenceRule::IRC_INEQUALITY_RESOLUTION, cl1, cl2));
                    auto size = cl1->size() + cl2->size() - 1 + (res.constraints ? res.constraints->size() : 0);
                    auto resolvent = new(size) Clause(size, inf);
                    //   ^^^^^^^^^--> gonna be k1 * rest1 + k2 * rest2 >= 0 \/ C1 \/ C2 \/ constraints
                    {
                      unsigned offset = 0;
                      auto push = [&](Literal* lit) { ASS(offset < size); (*resolvent)[offset++] = lit; };
                      
                      // push resolvent literal: k1 * rest1 + k2 * rest2 >= 0 
                      push(resolventLit.denormalize());

                      // push other literals from clause: C1 \/ C2
                      auto pushLiterals = 
                        [&](Clause& cl, Literal* skipLiteral, int result)
                        {
                          for (unsigned i = 0; i < cl.size(); i++) {
                            if (cl[i] != skipLiteral) {
                              push(subs.applyTo(cl[i], result));
                            }
                          }
                        };
                      pushLiterals(*cl1, literal1, 0);
                      pushLiterals(*cl2, literal2, 1);

                      // push constraints
                      if (res.constraints) {
                        for (auto l : UwaResult::cnstLiterals(*res.substitution, *res.constraints)) {
                            push(l);
                        }
                      }

                      ASS_EQ(offset, size)
                    }
                    DEBUG("  resolvent: ", *resolvent);
                    ASS(SortHelper::areSortsValid(resolvent))
                    env.statistics->ircIrCnt++;
                    return Option<Clause*>(resolvent);
                }));
    }));
}

ClauseIterator InequalityResolution::generateClauses(Clause* premise)
{
  CALL("InequalityResolution::generateClauses");
  DEBUG("in: ", *premise)

  return pvi(iterTraits(ownedArrayishIterator(_shared->strictlyMaxLiterals(premise)))
    .filterMap([=](Literal* lit) {
      return this->_shared->normalizeIneq(lit)
      .map([=](auto ineq) {
          return ineq.apply([=](auto ineq) {
              return generateClauses(premise, lit, ineq);
              });
          });

      })
    .flatten());
}

} // namespace IRC
} // namespace Inferences

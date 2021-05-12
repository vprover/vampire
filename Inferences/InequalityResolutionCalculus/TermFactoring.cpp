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

#include "Indexing/Index.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "TermFactoring.hpp"
#include "InequalityResolution.hpp"
#include "Kernel/PolynomialNormalizer.hpp"
#include "Kernel/InequalityResolutionCalculus.hpp"
#include "Indexing/TermIndexingStructure.hpp"
#include "Kernel/RobSubstitution.hpp"

#define DEBUG(...)  // DBG(__VA_ARGS__)

using Kernel::InequalityLiteral;

namespace Inferences {
namespace InequalityResolutionCalculus {

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

using Lib::TypeList::List;
using Lib::TypeList::Indices;
using Lib::TypeList::UnsignedList;

template<class F, class... Capt>
class Capture
{
  
  template<class... Args> using Result = typename std::result_of<F(Capt..., Args...)>::type;
  F _fun;
  std::tuple<Capt...> _capt;
public:
  Capture(F fun, Capt... capt) : _fun(std::move(fun)), _capt(std::forward<Capt>(capt)...) {}

  template<class... Args>
  Result<Args...> operator()(Args... args)
  { return apply(Indices<List<Args...>>{}, std::forward<Args>(args)...); }

  template<class... Args, int... idx>
  Result<Args...> apply(UnsignedList<idx...>, Args... args)
  { return _fun(std::get<idx>(_capt)..., std::forward<Args>(args)...); }
};

template<class F, class... Capt>
Capture<F, Capt...> capture(F f, Capt... capt) 
{ return Capture<F,Capt...>(std::move(f), capt...); }

#define OVERFLOW_SAFE 1

#define ASSERT_NO_OVERFLOW(...)                                                                               \
  [&]() { try { return __VA_ARGS__; }                                                                         \
          catch (MachineArithmeticException&) { ASSERTION_VIOLATION } }()                                     \

template<class NumTraits>
ClauseIterator TermFactoring::generateClauses(Clause* cl, Literal* literal) const
{

  CALL("TermFactoring::generateClauses(Clause*, Literal*) const")
  using Monom      = Monom<NumTraits>;
  using IrcLiteral = IrcLiteral<NumTraits>;

  auto litOpt = this->normalizer().normalizeIrc<NumTraits>(literal);
  if (litOpt.isNone()) 
    return ClauseIterator::getEmpty();

  // The rule we compute looks as follows for rat & real:
  //
  // num1 * term1 + num2 * term2 + rest > 0 \/ C1   
  // --------------------------------
  // ((num1 + num2) * term1  + rest > 0 ) \sigma \/ Const

  auto lit_ = std::move(litOpt).unwrap();
  if (lit_.overflowOccurred) {
    env.statistics->irOverflowNorm++;
    return ClauseIterator::getEmpty();
  }
  auto lit = lit_.value;
  //   ^^^--> num1 * term1 + num2 * term2 + rest > 0

  DEBUG("lit: ", lit)
  auto max = InequalityResolution::maxTerms(lit, ord());
  DEBUG("maximal terms: ", max)
  return pvi(iterTraits(getRangeIterator(0, ((int) max.size()) - 1))
    .flatMap([this, cl, lit, literal, max = Lib::make_unique<Stack<Monom>>(std::move(max))](unsigned i1) -> VirtualIterator<Clause*> { 
      auto mon1 = (*max)[i1];
      //   ^^^^ <--- num1 * term1 
      CALL("TermFactoring::generateClauses:@clsr1")
      return pvi(iterTraits(getRangeIterator(i1 + 1, (unsigned) max->size()))
        .filterMap([this, cl, lit, literal, mon1, i1, max = &*max](unsigned long i2) -> Option<Clause*> {
            CALL("TermFactoring::generateClauses:@clsr2")
            ASS_NEQ(i1,i2)

            auto mon2 = (*max)[i2];
            //   ^^^^ <--- num2 * term2 
            DEBUG("applying to ", mon1, " ", mon2)

            RobSubstitution subst;
            Stack<UnificationConstraint> consts;
            Kernel::UWAMismatchHandler hndlr(_shared->uwa, consts);
            if (!subst.unify(mon1.factors->denormalize(), /* var bank: */ 0, 
                             mon2.factors->denormalize(), /* var bank: */ 0,
                             &hndlr)) {
              return Option<Clause*>();
            }

            auto resolventTerm = Monom(mon1.numeral + mon2.numeral, mon1.factors);
            auto resolventSum = Stack<Monom>(lit.term().nSummands() - 1);
            resolventSum.push(resolventTerm);
            for (unsigned i = 0; i < lit.term().nSummands(); i++) {
              auto t = lit.term().summandAt(i);
              if (t != mon1 && t != mon2) 
                resolventSum.push(t);
            }

            auto sum = PolynomialEvaluation::simplifySummation(resolventSum);
            if (sum.overflowOccurred) {
              env.statistics->irOverflowApply++;
              return Option<Clause*>();
            }
            auto resolventLit = IrcLiteral(perfect(sum.value), lit.symbol());
            //   ^^^^^^^^^^^^--> (num1 + num2) * term1 + rest > 0

            Inference inf(GeneratingInference1(Kernel::InferenceRule::INEQUALITY_FACTORING, cl));
            auto size = cl->size() + consts.size();
            auto resolvent = new(size) Clause(size, inf);
            {
              unsigned offset = 0;
              auto push = [&](Literal* lit) { ASS(offset < size); (*resolvent)[offset++] = lit; };
              
              // push resolvent literal: k1 * rest1 + k2 * rest2 >= 0 
              push(subst.apply(resolventLit.denormalize(), 0));

              // push other literals from clause: C
              for (unsigned i = 0; i < cl->size(); i++) {
                if ((*cl)[i] != literal) {
                  push(subst.apply((*cl)[i], 0));
                }
              }

              // push constraints
              for (auto& c : consts) {

                auto toTerm = [&](pair<TermList, unsigned> const& weirdConstraintPair) -> TermList
                              { return subst.apply(weirdConstraintPair.first, weirdConstraintPair.second); };
                // t1\sigma != c2\simga
                auto sort = SortHelper::getResultSort(c.first.first.term());
                push(Literal::createEquality(false, toTerm(c.first), toTerm(c.second), sort));
              }


              ASS_EQ(offset, size)
            }
            DEBUG("in:  ", *cl)
            DEBUG("out: ", *resolvent)


            return Option<Clause*>(resolvent);

        }));

    }));
}

ClauseIterator TermFactoring::generateClauses(Clause* premise)
{
  CALL("TermFactoring::generateClauses");
  DEBUG("in: ", *premise)

  return pvi(iterTraits(premise->getSelectedLiteralIterator())
    .flatMap([=](Literal* lit) {
      CALL("TermFactoring::generateClauses@clsr1");
        return getConcatenatedIterator(getConcatenatedIterator(
              generateClauses< IntTraits>(premise, lit) ,
              generateClauses< RatTraits>(premise, lit)),
              generateClauses<RealTraits>(premise, lit));
    }));
}

} // namespace InequalityResolutionCalculus
} // namespace Inferences

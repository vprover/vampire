
/*
 * File InequalityResolution.cpp.
 *
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

#include "Indexing/Index.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "InequalityResolution.hpp"
#include "Shell/UnificationWithAbstractionConfig.hpp"
#include "Kernel/PolynomialNormalizer.hpp"
#include "Kernel/InequalityNormalizer.hpp"
#include "Indexing/TermIndexingStructure.hpp"
#define DEBUG(...) // DBG(__VA_ARGS__)

using Kernel::InequalityLiteral;
namespace Indexing {


template<class NumTraits>
bool InequalityResolutionIndex::handleLiteral(Literal* lit, Clause* c, bool adding)
{
  /* normlizing to t >= 0 */
  auto norm_ = this->normalizer().normalize<NumTraits>(lit);
  if (norm_.isSome()) {
    auto norm = norm_.unwrap();
    for (auto monom : norm.term().iterSummands()) {
      if (!monom.tryNumeral().isSome()) {

        auto term = monom.factors->denormalize();
        if (adding) {
          DEBUG("inserting: ", term);
          _is->insert(term, lit, c);
        } else {
          DEBUG("removing: ", term);
          _is->remove(term, lit, c);
        }
      }
    }
    return true;
  } else {
    return false;
  }
}

void InequalityResolutionIndex::handleClause(Clause* c, bool adding)
{
  CALL("InequalityResolutionIndex::handleClause");

  for (unsigned i = 0; i < c->size(); i++) {
    auto lit = (*c)[i];
    handleLiteral< IntTraits>(lit, c, adding) 
    || handleLiteral< RatTraits>(lit, c, adding)
    || handleLiteral<RealTraits>(lit, c, adding);
  }
}

}


namespace Inferences
{

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
	  _salg->getIndexManager()->request(INEQUALITY_RESOLUTION_SUBST_TREE) );
}

void InequalityResolution::detach()
{
  CALL("InequalityResolution::detach");
  ASS(_salg);

  _index=0;
  _salg->getIndexManager()->release(INEQUALITY_RESOLUTION_SUBST_TREE);
  GeneratingInferenceEngine::detach();
}


void InequalityResolution::setTestIndices(Stack<Indexing::Index*> const& indices)
{ _index = (InequalityResolutionIndex*) indices[0]; }


/* 
 * maps (num1, num2) -> (k1, k2) 
 * s.t.  num1 * k1 = - num2 * k2
 */
template<class Numeral>
pair<Numeral,Numeral> computeFactors(Numeral num1, Numeral num2)
{ 
  ASS(num1 != Numeral(0))
  ASS(num2 != Numeral(0))
  // num1 * k1 = - num2 * k2
  // let k1 = 1
  // ==> num1 = - num2 * k2 ==> k2 = - num1 / num2
  return std::make_pair(Numeral(1), -(num1 / num2));
}

/* 
 * maps (num1, num2) -> (k1, k2) 
 * s.t.  num1 * k1 = - num2 * k2
 */
pair<IntegerConstantType,IntegerConstantType> computeFactors(IntegerConstantType num1, IntegerConstantType num2)
{ 
  ASS(num1 != IntegerConstantType(0))
  ASS(num2 != IntegerConstantType(0))
  // num1 * k1 = - num2 * k2
  // let k1 =   num2 / gcd(num1, num2)
  //     k2 = - num1 / gcd(num1, num2)
  // num1 * num2 / gcd(num1, num2) = - num2 * (- num1 / gcd(num1, num2))
  auto gcd = IntegerConstantType::gcd(num1, num2);
  ASS(gcd.divides(num1));
  ASS(gcd.divides(num2));
  return num1.isNegative() ? std::make_pair( num2.quotientE(gcd), -num1.quotientE(gcd))
                           : std::make_pair(-num2.quotientE(gcd),  num1.quotientE(gcd));
}


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

template<class NumTraits> 
VirtualIterator<Monom<NumTraits>> InequalityResolution::maxTerms(InequalityLiteral<NumTraits> const& lit) const
{ 
  using Monom = Monom<NumTraits>;
  Stack<Monom> max(lit.term().nSummands()); // TODO not sure whether this size allocation brings an advantage
  auto monoms = lit.term().iterSummands().template collect<Stack>();
  for (unsigned i = 0; i < monoms.size(); i++) {
    auto isMax = true;
    for (unsigned j = 0; j < monoms.size(); j++) {
      auto cmp = ord()->compare(
          monoms[i].factors->denormalize(), 
          monoms[j].factors->denormalize());
      if (cmp == Ordering::LESS) {
          isMax = false;
          break;
      } else if(cmp == Ordering::EQUAL || cmp == Ordering::INCOMPARABLE || Ordering::GREATER) {
        /* ok */
      } else {
        ASSERTION_VIOLATION_REP(cmp)
      }
    }
    if (isMax) 
      max.push(monoms[i]);
  }
  return pvi(ownedArrayishIterator(std::move(max))); 
}

template<class NumTraits>
ClauseIterator InequalityResolution::generateClauses(Clause* cl1, Literal* lit1_) const
{
  CALL("InequalityResolution::generateClauses(Clause*, Literal*) const")
  using Monom             = Monom<NumTraits>;
  using MonomFactors      = MonomFactors<NumTraits>;
  using Numeral           = typename Monom::Numeral;
  using InequalityLiteral = InequalityLiteral<NumTraits>;
  const bool isInt        = std::is_same<NumTraits, IntTraits>::value;

  auto lit1Opt = this->normalizer().normalize<NumTraits>(lit1_);
  if (lit1Opt.isNone()) 
    return ClauseIterator::getEmpty();

  // The rule we compute looks as follows:
  //
  // num1 * term + rest1 >= 0 \/ C1      num2 * term2 + rest2 >= 0 \/ C2
  // --------------------------------------------------------------------
  //         k1 * rest1 + k2 * rest2 >= 0 \/ C1 \/ C2


  auto lit1 = lit1Opt.unwrap();
  //   ^^^^--> num1 * term + rest1 >= 0

  DEBUG("lit1: ", lit1)
  return pvi(iterTraits(maxTerms(lit1))
    .flatMap([this, cl1, lit1, lit1_](Monom monom)  -> VirtualIterator<Clause*> { 
      CALL("InequalityResolution::generateClauses:@clsr1")
      auto num1  = monom.numeral;
      auto term1 = monom.factors;
      DEBUG("monom1: ", monom)

      return pvi(iterTraits(_index->getUnificationsWithConstraints(term1->denormalize(), true))
                .filterMap([this, cl1, lit1, lit1_, num1, term1](TermQueryResult res) -> Option<Clause*> {
                  CALL("InequalityResolution::generateClauses:@clsr2")
                  auto& subs = *res.substitution;

                  auto cl2   = res.clause;
                  auto term2 = normalizeTerm(TypedTermList(res.term, NumTraits::sort))
                                .downcast<NumTraits>().unwrap()
                                ->tryMonom().unwrap()
                                .factors;
                  auto lit2_ = res.literal;
                  auto lit2  = this->normalizer().normalize<NumTraits>(lit2_).unwrap();
                  //   ^^^^ ~=  num2 * term2 + rest2 >= 0
                  DEBUG("resolving against: ", lit2, " (term: ", term2, ", constr: ", res.constraints, ")");

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

                  auto factors = computeFactors(num1, num2);
                  //   ^^^^^^^--> (k1, k2)
                  ASS_REP(factors.first.isPositive() && factors.second.isPositive(), factors)

                  Stack<Monom> resolventSum(lit1.term().nSummands() + lit2.term().nSummands() - 2 + (isInt ? 1 : 0));
                  //           ^^^^^^^^^^^^--> gonna be k1 * rest1 + k2 * rest2                   
                  {
                    auto pushTerms = [&](InequalityLiteral lit, Perfect<MonomFactors> termToSkip, Numeral num, bool resultVarBank)
                              {
                                resolventSum.loadFromIterator(lit.term()
                                    .iterSummands()
                                    .filter([&](Monom m) { return m.factors != termToSkip; })
                                    .map   ([&](Monom m) { 
                                      auto out = Monom(m.numeral * num, m.factors)
                                        .mapVars([&](Variable v) { 
                                          auto var = TermList::var(v.id());
                                          auto t = subs.applyTo(var, resultVarBank);
                                          return normalizeTerm(TypedTermList(t, NumTraits::sort)); 
                                        }); 
                                      return out;
                                    })
                                );
                              };

                    pushTerms(lit1, term1, factors.first , false);
                    pushTerms(lit2, term2, factors.second, true);
                    if (isInt) {
                      resolventSum.push(Monom(Numeral(-1)));
                    }
                  }

                  auto resolventLit = InequalityLiteral(perfect(PolynomialEvaluation::simplifySummation(resolventSum)), strictness);
                  //   ^^^^^^^^^^^^--> k1 * rest1 + k2 * rest2 >= 0

                  Inference inf(GeneratingInference2(Kernel::InferenceRule::INEQUALITY_RESOLUTION, cl1, cl2));
                  auto size = cl1->size() + cl2->size() - 1 + (res.constraints ? res.constraints->size() : 0);
                  auto resolvent = new(size) Clause(size, inf);
                  //   ^^^^^^^^^--> gonna be k1 * rest1 + k2 * rest2 >= 0 \/ C1 \/ C2 \/ constraints
                  {
                    unsigned offset = 0;
                    auto push = [&offset, &resolvent](Literal* lit) { (*resolvent)[offset++] = lit; };
                    
                    // push resolvent literal: k1 * rest1 + k2 * rest2 >= 0 
                    push(subs.applyToResult(subs.applyToResult(resolventLit.denormalize())));

                    // push other literals from clause: C1 \/ C2
                    auto pushLiterals = 
                      [&](Clause& cl, Literal* skipLiteral, bool result)
                      {
                        for (unsigned i = 0; i < cl.size(); i++) {
                          if (cl[i] != skipLiteral) {
                            push(subs.apply(cl[i], result));
                          }
                        }
                      };
                    pushLiterals(*cl1, lit1_, false);
                    pushLiterals(*cl2, lit2_, true);

                    // push constraints
                    if (res.constraints) {
                      for (auto& c : *res.constraints) {
                        auto toTerm = [&](pair<TermList, unsigned> const& weirdConstraintPair) -> TermList
                                      { return subs.applyTo(weirdConstraintPair.first, weirdConstraintPair.second); };
                        // t1\sigma != c2\simga
                        push(Literal::createEquality(false, toTerm(c.first), toTerm(c.second), NumTraits::sort));
                      }
                    }

                    ASS_EQ(offset, size)
                  }
                  DEBUG("resolvent: ", *resolvent);
                  return Option<Clause*>(resolvent);
                }));
    }));
}

ClauseIterator InequalityResolution::generateClauses(Clause* premise)
{
  CALL("InequalityResolution::generateClauses");

  return pvi(iterTraits(premise->getSelectedLiteralIterator())
    .flatMap([&](Literal* lit) {
        return getConcatenatedIterator(getConcatenatedIterator(
              generateClauses< IntTraits>(premise, lit) ,
              generateClauses< RatTraits>(premise, lit)),
              generateClauses<RealTraits>(premise, lit));
    }));
}

}

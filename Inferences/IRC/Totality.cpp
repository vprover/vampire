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
 * @file Totality.cpp
 * Defines class Totality
 *
 */

#include "Totality.hpp"
#include "Saturation/SaturationAlgorithm.hpp"
#include "Shell/Statistics.hpp"

#define TODO ASSERTION_VIOLATION

namespace Inferences {
namespace IRC {

////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// INDEXING STUFF
////////////////////////////////////////////////////////////////////////////////////////////////////////////////

void Totality::attach(SaturationAlgorithm* salg) 
{
  CALL("InequalityResolution::attach");
  ASS(!_index);

  GeneratingInferenceEngine::attach(salg);
  _index=static_cast<InequalityResolutionIndex*> (
	  _salg->getIndexManager()->request(IRC_INEQUALITY_RESOLUTION_SUBST_TREE) );
  _index->setShared(_shared);
}

void Totality::detach() 
{
  CALL("InequalityResolution::detach");
  ASS(_salg);

  _index=0;
  _salg->getIndexManager()->release(IRC_INEQUALITY_RESOLUTION_SUBST_TREE);
  GeneratingInferenceEngine::detach();
}

#if VDEBUG
void Totality::setTestIndices(Stack<Indexing::Index*> const& indices)
{
  _index = (InequalityResolutionIndex*) indices[0]; 
  _index->setShared(_shared);
}
#endif

////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// actual rule
////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//
// C1 \/ j s1 + t1 ≥ 0                C2 \/ −k s2 + t2 ≥ 0 
// =======================================================
// (C1 \/ C2 \/ k t1 + j t2  ̸≈ 0 \/ js1 + t1 ≈ 0)σ \/ Cnst
//
// where
// • uwa(s1,s2) = ⟨σ,Cnst⟩
// • s1σ is strictly maximal in terms(s1 + t1)σ
// • s2σ is strictly maximal in terms(s2 + t2)σ
// • ( j s1 + t1 ≥ 0)σ is strictly maximal in Hyp1σ .
// • (−k s2 + t2 ≥ 0)σ is strictly maximal in Hyp2σ

template<class NumTraits> Clause* Totality::applyRule(
    Clause* hyp1, Literal* lit1, IrcLiteral<NumTraits> l1, Monom<NumTraits> j_s1,
    Clause* hyp2, Literal* lit2, IrcLiteral<NumTraits> l2, Monom<NumTraits> k_s2,
    ResultSubstitution& sigma_, Stack<UnificationConstraint>& cnst
    ) const 
{
  env.statistics->ircTotCnt++;
  auto sigma = [&](auto t, int varBank) { return sigma_.applyTo(t, varBank); };
  auto j = j_s1.numeral;
  auto k = k_s2.numeral;

  Stack<Literal*> conclusion(hyp1->size() + hyp2->size() + cnst.size());

  auto C1_sigma = iterTraits(hyp1->getLiteralIterator())
    .filter([&](auto lit) { return lit != lit1; })
    .map   ([&](auto lit) { return sigma(lit, 0); });

  auto C2_sigma = iterTraits(hyp2->getLiteralIterator())
    .filter([&](auto lit) { return lit != lit2; })
    .map   ([&](auto lit) { return sigma(lit, 1); });

  conclusion.loadFromIterator(getConcatenatedIterator(C1_sigma, C2_sigma));

  if (l1.term().nSummands() > 1 || l2.term().nSummands() > 1 ) {

    auto k_t1 = l1.term().iterSummands()
              .filter([&](auto t) { return t != j_s1; })
              .map([&](auto t) { return  sigma((-k * t).denormalize(), 0); });

    auto j_t2 = l2.term().iterSummands()
              .filter([&](auto t) { return t != k_s2; })
              .map([&](auto t) { return  sigma((j * t).denormalize(), 1); });

    auto resolvent1 = NumTraits::eq(false, NumTraits::sum(getConcatenatedIterator(k_t1, j_t2)), NumTraits::zero());
    //   ^^^^^^^^^^ --> (k t1 + j t2  ̸≈ 0)σ

    conclusion.push(resolvent1);
  } else {
    // we do not add the redundnat literal `0 != 0`
  }

  auto resolvent2 = NumTraits::eq(true, sigma(l1.term().denormalize(), 0), NumTraits::zero());
  //   ^^^^^^^^^^----> (js1 + t1 ≈ 0)σ
  conclusion.push(resolvent2);

  conclusion.loadFromIterator(UwaResult::cnstLiterals(sigma_, cnst));

  Inference inf(GeneratingInference2(Kernel::InferenceRule::IRC_TOTALITY, hyp1, hyp2));
  return Clause::fromStack(conclusion, inf);
}


ClauseIterator Totality::generateClauses(Clause* premise) 
{
  auto maxLiterals = make_shared(new Stack<Literal*>(_shared->strictlyMaxLiterals(premise))); // TODO use Set instead of Stack
  return pvi(numTraitsIter([this, premise,maxLiterals](auto numTraits){
    using NumTraits = decltype(numTraits);
    return iterTraits(ownedArrayishIterator(_shared->maxAtomicTermsNonVar<NumTraits>(premise)))
    // return iterTraits(ownedArrayishIterator(_shared->strictlyMaxLiterals(premise)))
      .filter([maxLiterals](auto& maxTerm) 
          { return iterTraits(maxLiterals->iterFifo())
                     .find([&](auto x) { return x == maxTerm.literal; })
                     .isSome(); })
      .filter([](auto maxTerm) { return maxTerm.ircLit.symbol() == IrcPredicate::GREATER_EQ; })
      .flatMap([this, premise](auto maxTerm) 
          { return this->generateClauses(premise, maxTerm.literal, maxTerm.ircLit, maxTerm.self); });
  }));

  // return pvi(iterTraits(ownedArrayishIterator(_shared->strictlyMaxLiterals(premise)))
  //   .filterMap([=](auto lit1) { return _shared->normalize(lit1).map([&](auto norm) { return make_pair(lit1, norm); }); })
  //   .filter([](auto l1) { return l1.second.apply([&](auto l1) { return l1.symbol() == IrcPredicate::GREATER_EQ; }); })
  //   .flatMap([=](auto lit1_l1) 
  //     { return lit1_l1.second.apply([&](auto l1) { return generateClauses(premise, lit1_l1.first, l1); }); })
  // );
}

template<class NumTraits> 
ClauseIterator Totality::generateClauses(Clause* hyp1, Literal* lit1, IrcLiteral<NumTraits> l1, Monom<NumTraits> j_s1) const
{
  // return pvi(iterTraits(ownedArrayishIterator(_shared->maxAtomicTerms(l1)))
  //     .flatMap([=](Monom<NumTraits> j_s1) {
        return pvi(iterTraits(_index->getUnificationsWithConstraints(j_s1.factors->denormalize(), true))
            .filterMap([=](TermQueryResult unif) {
              auto hyp2 = unif.clause;
              auto lit2 = unif.literal;
              auto l2 = _shared->normalize(lit2)
                .unwrap()
                .template unwrap<decltype(l1)>();

              auto s2 = _shared->normalize(TypedTermList(unif.term, NumTraits::sort()))
                .downcast<NumTraits>().unwrap()->tryMonom().unwrap()
                .factors;

              Monom<NumTraits> k_s2 = l2.term()
                .iterSummands()
                .find([&](auto monom) { return monom.factors == s2; })
                .unwrap();

              if (l2.symbol() != IrcPredicate::GREATER_EQ)
                return Option<Clause*>();

              if (j_s1.numeral.isNegative() || k_s2.numeral.isPositive())
                return Option<Clause*>();

              // TODO check maximality conditions here

              Stack<UnificationConstraint> constr;
              return Option<Clause*>(applyRule(hyp1, lit1, l1, j_s1,
                                               hyp2, lit2, l2, k_s2,
                                               *unif.substitution, unif.constraints.isEmpty() ? constr : *unif.constraints ));
            })
        );
      // })
      // );
}

} // namespace IRC 
} // namespace Inferences 

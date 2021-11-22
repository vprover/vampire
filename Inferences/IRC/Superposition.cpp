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
 * @file Superposition.cpp
 * Defines class Superposition
 *
 */

#include "Superposition.hpp"
#include "Saturation/SaturationAlgorithm.hpp"
#include "Shell/Statistics.hpp"
#include "Kernel/EqHelper.hpp"

#define ORDERING_ASSERTIONS 1
#if ORDERING_ASSERTIONS 
#  define ORD_CHECK(...) ASS(__VA_ARGS__)
#else 
#  define ORD_CHECK(...) if (!(__VA_ARGS__)) return nothing;
#endif // ORDERING_ASSERTIONS

namespace Inferences {
namespace IRC {

void Superposition::attach(SaturationAlgorithm* salg) 
{ 
  CALL("Superposition::attach");
  ASS(!_indexRhs);
  ASS(!_indexLhs);

  GeneratingInferenceEngine::attach(salg);

  _indexLhs=static_cast<IRCSuperpositionLhsIndex*> (
	  _salg->getIndexManager()->request(IRC_SUPERPOSITION_LHS_SUBST_TREE) );
  _indexLhs->setShared(_shared);

  _indexRhs=static_cast<IRCSuperpositionRhsIndex*> (
	  _salg->getIndexManager()->request(IRC_SUPERPOSITION_RHS_SUBST_TREE) );
  _indexRhs->setShared(_shared);

}

void Superposition::detach() 
{
  CALL("Superposition::detach");
  ASS(_salg);

  _indexLhs=0;
  _salg->getIndexManager()->release(IRC_SUPERPOSITION_LHS_SUBST_TREE);
  _indexRhs=0;
  _salg->getIndexManager()->release(IRC_SUPERPOSITION_RHS_SUBST_TREE);
  GeneratingInferenceEngine::detach();
}

// ClauseIterator Superposition::generateClauses(Clause* premise) 
// {
//   auto maxLits = make_shared(new Stack<Literal*>(_shared->strictlyMaxLiterals(premise)));
//   return pvi(numTraitsIter([this, premise, maxLits](auto numTraits) {
//      return iterTraits(ownedArrayishIterator(_shared->maxAtomicTermsNonVar<decltype(numTraits)>(premise)))
//        .filter([maxLits](auto maxTerm) 
//            { return iterTraits(maxLits->iterFifo())
//                       .find([&](auto x) 
//                           { return x == maxTerm.literal; })
//                       .isSome(); })
//        .filterMap([this, premise](auto maxTerm) { return this->genLhs(premise, maxTerm.literal, maxTerm.ircLit, maxTerm.self); })
//        .flatten();
//   }));
// }


// ClauseIterator Superposition::generateClauses(Clause* premise) 
// {
//   auto maxLits = make_shared(new Stack<Literal*>(_shared->strictlyMaxLiterals(premise)));
//   return pvi(numTraitsIter([this, premise, maxLits](auto numTraits) {
//      return iterTraits(ownedArrayishIterator(_shared->maxAtomicTermsNonVar<decltype(numTraits)>(premise)))
//        .filter([maxLits](auto maxTerm) 
//            { return iterTraits(maxLits->iterFifo())
//                       .find([&](auto x) 
//                           { return x == maxTerm.literal; })
//                       .isSome(); })
//        .filterMap([this, premise](auto maxTerm) { return this->generateClauses(premise, maxTerm.literal, maxTerm.ircLit, maxTerm.self); })
//        .flatten();
//   }));
// }

  

#if VDEBUG
void Superposition::setTestIndices(Stack<Indexing::Index*> const& indices) 
{
  _indexLhs = (IRCSuperpositionLhsIndex*) indices[0]; 
  _indexLhs->setShared(_shared);
  _indexRhs = (IRCSuperpositionRhsIndex*) indices[1]; 
  _indexRhs->setShared(_shared);
}
#endif

// C1 \/ ±ks1+t1 ≈ 0            C2 \/ u[s2]+t2 <> 0
// ================================================
//   (C1 \/ C2 \/ u[∓(1/k)t1]+t2 <> 0) σ \/ Cnst
// where
// • uwa(s1,s2)=⟨σ,Cnst⟩
// • <>  ∈ {>,≥,≈,̸≈}
// •        s1  σ is strictly maximal in terms(s1 + t1)σ
// • term(u[s2])σ is strictly maximal in terms(u[s2] + t2)σ 
// • (±k. s1 + t1 ≈ 0)σ is strictly maximal in Hyp1σ
// • ( u[s2] + t2 ≈ 0)σ is strictly maximal in Hyp2σ
// • Hyp2σ is strictly maximal in {Hyp1, Hyp2}σ.
template<class NumTraits> Option<Clause*> Superposition::applyRule(
    Clause* hyp1,            // <- `C1 \/ ±ks1+t1 ≈ 0` 
    Literal* pivot1,         // <-       `±ks1+t1 ≈ 0` 
    IrcLiteral<NumTraits> eq,// <-       `±ks1+t1 ≈ 0` 
    Monom<NumTraits> k_s1,   // <-       `±ks1` 
    Clause* hyp2,        // <- `C2 \/ u[s2]+t2 <> 0` 
    Literal* pivot2,     // <-       `u[s2]+t2 <> 0` 
    TermList s2,         // <-       `s2` 
    ResultSubstitutionSP& res_substitution,
    UnificationConstraintStackSP& res_constraints,
    int bank1
    ) const 
{
  using Numeral = typename NumTraits::ConstantType;
  Option<Clause*> nothing;
  ASS(s2.isTerm())
  ASS(bank1 == 0 || bank1 == 1)

  auto s1 = k_s1.factors; 
  Stack<UnificationConstraint> dummy;
  auto& cnst = res_constraints ? *res_constraints : dummy;
  auto sigma = [&](auto term, int varBank) { return res_substitution->applyTo(term, bank1 == 0 ? varBank : 1 - varBank); };

  // maximality checks
  {
    // • ±k. s1 + t1 ≈ 0 is strictly maximal in Hyp1
    ORD_CHECK(_shared->strictlyMaximal(pivot1, hyp1->getLiteralIterator()))
    // • (±k. s1 + t1 ≈ 0)σ is strictly maximal in Hyp1σ
    if(!_shared->strictlyMaximal(sigma(pivot1, 0), iterTraits(hyp1->getLiteralIterator()).map([&](auto lit) { return sigma(lit, 0); }))) return nothing;

    // • u[s2] + t2 ≈ 0 is strictly maximal in Hyp2
    ASS(_shared->strictlyMaximal(pivot2, hyp2->getLiteralIterator()))
    // • ( u[s2] + t2 ≈ 0)σ is strictly maximal in Hyp2σ
    if(!_shared->strictlyMaximal(sigma(pivot2, 1), iterTraits(hyp2->getLiteralIterator()).map([&](auto lit) { return sigma(lit, 1); }))) return nothing;

    // •        s1   is strictly maximal in terms(s1 + t1)
    ORD_CHECK(_shared->strictlyMaximal(s1->denormalize(), eq.term().iterSummands().map([&](auto monom) { return monom.factors->denormalize(); })))
    // •        s1  σ is strictly maximal in terms(s1 + t1)σ
    if(!_shared->strictlyMaximal(sigma(s1->denormalize(), 0), eq.term().iterSummands().map([&](auto monom) { return sigma(monom.factors->denormalize(), 0); }))) { return nothing; }

    // • term(u[s2])σ is strictly maximal in terms(u[s2] + t2)σ 
    // TODO check this condition somehow ?!
    // • Hyp2σ is strictly maximal in {Hyp1, Hyp2}σ.
    // TODO check this condition somehow ?!
  }

  Stack<Literal*> concl(hyp1->size() - 1 // <- C1
      + hyp2->size() - 1 // <- C2
      + 1                // <- u[∓(1/k)t1]+t2 <> 0
      + cnst.size());    // <- Cnst


  // adding C1
  for (auto lit : iterTraits(hyp1->getLiteralIterator())) {
    if (lit != pivot1)
      concl.push(sigma(lit, 0));
  }

  // adding C2
  for (auto lit : iterTraits(hyp2->getLiteralIterator())) {
    if (lit != pivot2)
      concl.push(sigma(lit, 1));
  }

  // adding u[∓(1/k)t1]+t2 <> 0) σ 
  {
    auto k = k_s1.numeral;
    auto repl = NumTraits::sum(eq.term().iterSummands()
    //   ^^^^ -> u[∓(1/k)t1]+t2 <> 0) σ 
        .filter([&](auto t) { return t != k_s1; })
        .map([&](auto monom) { return ((Numeral(-1) / k) * monom).denormalize(); }));

    auto resolvent = EqHelper::replace(sigma(pivot2, 1), sigma(s2, 1), repl);
    concl.push(resolvent);
  }

  // adding Cnst
  concl.loadFromIterator(UwaResult::cnstLiterals(*res_substitution, cnst));

  env.statistics->ircSupCnt++;
  Inference inf(GeneratingInference2(Kernel::InferenceRule::IRC_SUPERPOSITION, hyp1, hyp2));
  return Option<Clause*>(Clause::fromStack(concl, inf));
}

template<class NumTraits> Option<ClauseIterator> Superposition::genRhs(
    Clause* hyp2,        // <- `C2 \/ u[s2]+t2 <> 0` 
    Literal* pivot2,     // <-       `u[s2]+t2 <> 0` 
    TermList s2 // <-       `s2` 
    ) const 
{
  ASS(s2.isTerm())
  ASS_EQ(SortHelper::getResultSort(s2.term()), NumTraits::sort())
  return Option<ClauseIterator>(
          pvi(iterTraits(pvi(this->_indexLhs->getUnificationsWithConstraints(s2, true)))
              .filterMap([=](TermQueryResult res) -> Option<Clause*> {

                auto hyp1 = res.clause;    // <- `C1 \/ ±ks1+t1 ≈ 0`
                auto pivot1 = res.literal; // <-       `±ks1+t1 ≈ 0`
                auto s1 = res.term; 
                auto eq = _shared->normalizer.normalizeIrc<NumTraits>(pivot1).unwrap().value;
                ASS_EQ(eq.symbol(), IrcPredicate::EQ)
                auto k_s1 = eq.term().iterSummands()
                  .find([&](auto monom) { return monom.factors->denormalize() == s1;  })
                  .unwrap();

                return applyRule<NumTraits>(
                    hyp1, pivot1, eq, k_s1,
                    hyp2, pivot2, s2, 
                    res.substitution, res.constraints, 1);
              })
          ));
}

template<class NumTraits> Option<ClauseIterator> Superposition::genLhs(
    Clause* hyp1,            // <- `C1 \/ ±ks1+t1 ≈ 0` 
    Literal* pivot1,         // <-       `±ks1+t1 ≈ 0` 
    IrcLiteral<NumTraits> eq,// <-       `±ks1+t1 ≈ 0` 
    Monom<NumTraits> k_s1    // <-       `±ks1` 
    ) const 
{
  if (eq.symbol() != IrcPredicate::EQ) {
    return Option<ClauseIterator>();
  }
  return Option<ClauseIterator>(
          pvi(iterTraits(pvi(this->_indexRhs->getUnificationsWithConstraints(k_s1.factors->denormalize(), true)))
              .filterMap([=](TermQueryResult res) -> Option<Clause*> {

                auto hyp2 = res.clause;    // <- `C2 \/ u[s2]+t2 <> 0`
                auto pivot2 = res.literal; // <-       `u[s2]+t2 <> 0`
                auto s2 = res.term; 
                
                return applyRule<NumTraits>(
                    hyp1, pivot1, eq, k_s1,
                    hyp2, pivot2, s2, 
                    res.substitution, res.constraints, 0);
              })
          ));
}

ClauseIterator Superposition::genRhs(IntTraits, Clause* premise, Lib::shared_ptr<Stack<Literal*>> maxLits)
{ return ClauseIterator::getEmpty(); }

ClauseIterator Superposition::genLhs(IntTraits, Clause* premise, Lib::shared_ptr<Stack<Literal*>> maxLits)
{ return ClauseIterator::getEmpty(); }

template<class NumTraits> ClauseIterator Superposition::genLhs(NumTraits, Clause* premise, Lib::shared_ptr<Stack<Literal*>> maxLits)
{
  return pvi(iterTraits(ownedArrayishIterator(_shared->maxAtomicTermsNonVar<NumTraits>(premise)))
       .filter([maxLits](auto maxTerm) 
           { return iterTraits(maxLits->iterFifo())
                      .find([&](auto x) 
                          { return x == maxTerm.literal; })
                      .isSome(); })
       .filterMap([this, premise](auto maxTerm) { return this->genLhs(premise, maxTerm.literal, maxTerm.ircLit, maxTerm.self); })
       .flatten());
}


template<class NumTraits> ClauseIterator Superposition::genRhs(NumTraits, Clause* hyp2, Lib::shared_ptr<Stack<Literal*>> maxLits)
{
  return pvi(
      iterTraits(maxLits->iterFifo())
        .flatMap([=](auto pivot2) { 
          return pvi(iterTraits(vi(new SubtermIterator(pivot2)))
            .filter([=](auto t) {
                if (t.isTerm()) {
                  auto f = t.term()->functor();
                  return SortHelper::getResultSort(t.term()) == NumTraits::sort()
                      && f != NumTraits::addF()
                      && f != NumTraits::mulF()
                      && !NumTraits::isNumeral(t);
                } else return false;
              })
            .filterMap([=](auto s2) {
              return genRhs<NumTraits>(hyp2, pivot2, s2);
            })
            .flatten());
        })
      );
}

ClauseIterator Superposition::generateClauses(Clause* premise) 
{
  auto maxLits = make_shared(new Stack<Literal*>(_shared->strictlyMaxLiterals(premise)));
  return pvi(numTraitsIter([this, premise, maxLits](auto numTraits) {
     return Lib::getConcatenatedIterator(
         genLhs(numTraits, premise, maxLits),
         genRhs(numTraits, premise, maxLits));
  }));
}

} // namespace IRC 
} // namespace Inferences 

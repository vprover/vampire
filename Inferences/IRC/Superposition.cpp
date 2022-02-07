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
      Hyp1<NumTraits> hyp1,
      Hyp2<NumTraits> hyp2,
    ResultSubstitutionSP& res_substitution,
    UnificationConstraintStackSP& res_constraints,
    int bank1
    ) const 
{
  MeasureTime time(env.statistics->ircSup);

  ASS (hyp1.eq.symbol() == IrcPredicate::EQ) 
  auto k_s1 = hyp1.k_s1;
  auto s2 = hyp2.s2;
  using Numeral = typename NumTraits::ConstantType;
  auto nothing = [&]() {
    time.applicationCancelled();
    return Option<Clause*>();
  };
  ASS(s2.isTerm())
  ASS(bank1 == 0 || bank1 == 1)

  auto s1 = k_s1.factors; 
  Stack<UnificationConstraint> dummy;
  auto& cnst = res_constraints ? *res_constraints : dummy;
  auto sigma = [&](auto term, int varBank) { return res_substitution->applyTo(term, bank1 == 0 ? varBank : 1 - varBank); };

  // maximality checks
  {
    // • ±k. s1 + t1 ≈ 0 is strictly maximal in Hyp1
    ASS(_shared->strictlyMaximal(hyp1.pivot, hyp1.cl->getLiteralIterator()))
    // • (±k. s1 + t1 ≈ 0)σ is strictly maximal in Hyp1σ
    if(!_shared->strictlyMaximal(sigma(hyp1.pivot, 0), iterTraits(hyp1.cl->getLiteralIterator()).map([&](auto lit) { return sigma(lit, 0); }))) return nothing();

    // • u[s2] + t2 ≈ 0 is strictly maximal in Hyp2
    ASS(_shared->strictlyMaximal(hyp2.pivot, hyp2.cl->getLiteralIterator()))
    // • ( u[s2] + t2 ≈ 0)σ is strictly maximal in Hyp2σ
    if(!_shared->strictlyMaximal(sigma(hyp2.pivot, 1), iterTraits(hyp2.cl->getLiteralIterator()).map([&](auto lit) { return sigma(lit, 1); }))) return nothing();

    // •        s1   is strictly maximal in terms(s1 + t1)
    ASS(_shared->strictlyMaximal(s1->denormalize(), hyp1.eq.term().iterSummands().map([&](auto monom) { return monom.factors->denormalize(); })))
    // •        s1  σ is strictly maximal in terms(s1 + t1)σ
    if(!_shared->strictlyMaximal(sigma(s1->denormalize(), 0), hyp1.eq.term().iterSummands().map([&](auto monom) { return sigma(monom.factors->denormalize(), 0); }))) { return nothing(); }

    // • term(u[s2])σ is strictly maximal in terms(u[s2] + t2)σ 
    // TODO check this condition somehow ?!
    // • Hyp2σ is strictly maximal in {Hyp1, Hyp2}σ.
    // TODO check this condition somehow ?!
  }

  Stack<Literal*> concl(hyp1.cl->size() - 1 // <- C1
      + hyp2.cl->size() - 1 // <- C2
      + 1                // <- u[∓(1/k)t1]+t2 <> 0
      + cnst.size());    // <- Cnst


  // adding C1
  for (auto lit : iterTraits(hyp1.cl->getLiteralIterator())) {
    if (lit != hyp1.pivot)
      concl.push(sigma(lit, 0));
  }

  // adding C2
  for (auto lit : iterTraits(hyp2.cl->getLiteralIterator())) {
    if (lit != hyp2.pivot)
      concl.push(sigma(lit, 1));
  }

  // adding u[∓(1/k)t1]+t2 <> 0) σ 
  {
    auto k = k_s1.numeral;
    auto repl = NumTraits::sum(hyp1.eq.term().iterSummands()
    //   ^^^^ -> ∓(1/k)t1 
        .filter([&](auto t) { return t != k_s1; })
        .map([&](auto monom) { return ((Numeral(-1) / k) * monom).denormalize(); }));

    auto resolvent = EqHelper::replace(sigma(hyp2.pivot, 1), sigma(s2, 1), sigma(repl, 0));
    //   ^^^^^^^^^ -> (u[∓(1/k)t1]+t2 <> 0) σ 
    concl.push(resolvent);
  }

  // adding Cnst
  concl.loadFromIterator(UwaResult::cnstLiterals(*res_substitution, cnst));

  Inference inf(GeneratingInference2(Kernel::InferenceRule::IRC_SUPERPOSITION, hyp1.cl, hyp2.cl));
  return Option<Clause*>(Clause::fromStack(concl, inf));
}

template<class NumTraits> auto Superposition::genRhs(Hyp2<NumTraits> hyp2) const 
{
  ASS(hyp2.s2.isTerm())
  ASS_EQ(SortHelper::getResultSort(hyp2.s2.term()), NumTraits::sort())
  return iterTraits(pvi(this->_indexLhs->getUnificationsWithConstraints(hyp2.key(), true)))
              .filterMap([=](TermQueryResult res) {
                return applyRule<NumTraits>(
                    Hyp1<NumTraits>::fromQueryResult(_shared, res), hyp2,
                    res.substitution, res.constraints, 1);
              });
}

template<class NumTraits> auto Superposition::genLhs(Hyp1<NumTraits> hyp1) const 
{
  return iterTraits(pvi(this->_indexRhs->getUnificationsWithConstraints(hyp1.key(), true)))
              .filterMap([=](TermQueryResult res) -> Option<Clause*> {

                return applyRule<NumTraits>(
                    hyp1, Hyp2<NumTraits>::fromQueryResult(_shared, res),
                    res.substitution, res.constraints, 0);
              });
}

auto Superposition::genRhs(IntTraits, Clause* premise, Lib::shared_ptr<Stack<Literal*>> const& maxLits)
{ return ClauseIterator::getEmpty(); }

auto Superposition::genLhs(IntTraits, Clause* premise, Lib::shared_ptr<Stack<Literal*>> const& maxLits)
{ return ClauseIterator::getEmpty(); }

template<class NumTraits> auto Superposition::genLhs(NumTraits numTraits, Clause* premise, Lib::shared_ptr<Stack<Literal*>> const& maxLits)
{
  return iterHyp1Apps(_shared, numTraits, premise, maxLits)
          .flatMap([&](auto hyp1) { return pvi(this->genLhs(hyp1)); });
}

template<class NumTraits> auto Superposition::genRhs(NumTraits numTraits, Clause* hyp2, Lib::shared_ptr<Stack<Literal*>> const& maxLits)
{
  return iterHyp2Apps(_shared, numTraits, hyp2, maxLits)
          .flatMap([&](auto hyp2) { return pvi(genRhs(hyp2)); });
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

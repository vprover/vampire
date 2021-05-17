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
#include "Kernel/EqHelper.hpp"

#define TODO ASSERTION_VIOLATION

namespace Inferences {
namespace IRC {

void Superposition::attach(SaturationAlgorithm* salg) 
{ 
  CALL("Superposition::attach");
  ASS(!_index);

  GeneratingInferenceEngine::attach(salg);
  _index=static_cast<IRCSuperpositionIndex*> (
	  _salg->getIndexManager()->request(IRC_SUPERPOSITION_SUBST_TREE) );
  _index->setShared(_shared);
}

void Superposition::detach() 
{
  CALL("Superposition::detach");
  ASS(_salg);

  _index=0;
  _salg->getIndexManager()->release(IRC_SUPERPOSITION_SUBST_TREE);
  GeneratingInferenceEngine::detach();
}

ClauseIterator Superposition::generateClauses(Clause* premise) 
{

    
  return pvi(
      iterTraits(premise->getSelectedLiteralIterator())
      .filterMap([this, premise](auto lit) -> Option<ClauseIterator> {
        return _shared->normalize(lit)
        .andThen([this, premise, lit](auto unsortedLit) -> Option<ClauseIterator> {
            return unsortedLit.apply([this, premise, lit](auto sortedLit) { return this->generateClauses(premise, lit, sortedLit); });
            });
        })
      .flatMap([=](auto x) { return x; })
      );
}

  

#if VDEBUG
void Superposition::setTestIndices(Stack<Indexing::Index*> const& indices) 
{
  _index = (IRCSuperpositionIndex*) indices[0]; 
  _index->setShared(_shared);
}
#endif

// C1 \/ ±ks1+t1 ≈ 0            C2 \/ u[s2]+t2 <> 0
// ================================================
//   (C1 \/ C2 \/ u[∓(1/k)t1]+t2 <> 0) σ \/ Cnst
// where
// • uwa(s1,s2)=⟨σ,Cnst⟩
// • <>  ∈ {>,≥,≈,̸≈}
// • term(s1) is strictly maximal in terms(s1 + t1)
// • term(u[s2]) is strictly maximal in terms(u[s2] + t2) • ±k. s1 + t1 ≈ 0 is strictly maximal in Hyp1
// • u[s2] + t2 ≈ 0 is strictly maximal in Hyp2
// • Hyp2 is strictly maximal in {Hyp1, Hyp2}.

template<class NumTraits> Option<ClauseIterator> Superposition::generateClauses(Clause* hyp1, Literal* pivot1, IrcLiteral<NumTraits> eq) const 
{
  using Numeral = typename NumTraits::ConstantType;
  if (eq.symbol() != IrcPredicate::EQ) {
    return Option<ClauseIterator>();
  }
  return Option<ClauseIterator>(
      pvi(iterTraits(ownedArrayishIterator(_shared->maxAtomicTerms(eq)))
        .flatMap([=](auto k_s1) { 
          return pvi(iterTraits(pvi(this->_index->getUnificationsWithConstraints(k_s1.factors->denormalize(), true)))
              .map([=](TermQueryResult res) -> Clause* {
                Stack<UnificationConstraint> dummy;

                auto hyp2 = res.clause;
                auto pivot2 = res.literal; 
                auto s2 = res.term; 
                auto& cnst = res.constraints ? *res.constraints : dummy;
                auto sigma = [&](auto term, int varBank) { return res.substitution->applyTo(term, varBank); };

                // TODO maximality check after unification

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
                  auto t1 = NumTraits::sum(eq.term().iterSummands()
                      .filter([&](auto t) { return t != k_s1; })
                      .map([](auto monom) { return monom.denormalize(); }));
                  auto k = k_s1.numeral;
                  auto repl = k != Numeral(-1) ? NumTraits::mul(NumTraits::constantTl(Numeral(-1) / k), sigma(t1, 0))
                                               :                                                        sigma(t1, 0) ;

                  auto resolvent = EqHelper::replace(sigma(pivot2, 1), sigma(s2, 1), repl);
                  concl.push(resolvent);
                }

                // adding Cnst
                concl.loadFromIterator(UwaResult::cnstLiterals(*res.substitution, cnst));

                Inference inf(GeneratingInference2(Kernel::InferenceRule::IRC_SUPERPOSITION, hyp1, hyp2));
                return Clause::fromStack(concl, inf);
              })
          )
            ;


        })
  )
  ) ;
}

Option<ClauseIterator> Superposition::generateClauses(Clause* hyp1, Literal* pivot1, IrcLiteral<IntTraits> eq) const 
{ return Option<ClauseIterator>(); } 

} // namespace IRC 
} // namespace Inferences 

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

#define DEBUG(...) // DBG(__VA_ARGS__)

namespace Inferences {
namespace IRC {

void Superposition::attach(SaturationAlgorithm* salg) 
{ 
  CALL("Superposition::attach");
  ASS(!_rhs);
  ASS(!_lhs);

  GeneratingInferenceEngine::attach(salg);

  _lhs=static_cast<decltype(_lhs)> (_salg->getIndexManager()
      ->request(IRC_SUPERPOSITION_LHS_SUBST_TREE) );
  _lhs->setShared(_shared);

  _rhs=static_cast<decltype(_rhs)>(_salg->getIndexManager()
      ->request(IRC_SUPERPOSITION_RHS_SUBST_TREE));
  _rhs->setShared(_shared);

}

void Superposition::detach() 
{
  CALL("Superposition::detach");
  ASS(_salg);

  _lhs=0;
  _salg->getIndexManager()->release(IRC_SUPERPOSITION_LHS_SUBST_TREE);
  _rhs=0;
  _salg->getIndexManager()->release(IRC_SUPERPOSITION_RHS_SUBST_TREE);
  GeneratingInferenceEngine::detach();
}
  

#if VDEBUG
void Superposition::setTestIndices(Stack<Indexing::Index*> const& indices) 
{
  _lhs = (decltype(_lhs)) indices[0]; 
  _lhs->setShared(_shared);
  _rhs = (decltype(_rhs)) indices[1]; 
  _rhs->setShared(_shared);
}
#endif
template<class A>
auto output_to_string(A const& a) {
  vstringstream out;
  out << a;
  return out.str();
}

// C1 \/ s1 ≈ t             C2 \/ L[s2]
// ====================================
//   (C1 \/ C2 \/ L[t])σ \/ Cnst
// where
// • uwa(s1,s2)=⟨σ,Cnst⟩
// • (s1 ≈ t)σ /⪯ C1σ
// •    L[s2]σ  ∈ Lit+ and L[s2]σ /⪯ C2σ
//   or L[s2]σ /∈ Lit+ and L[s2]σ /≺ C2σ
// • s2σ ⊴ x ∈ active(L[s2]σ)
// • s1σ /⪯ tσ
// • s1 is not a variable
// • s2 is not a variable
Option<Clause*> Superposition::applyRule(
    Lhs const& lhs, unsigned lhsVarBank,
    Rhs const& rhs, unsigned rhsVarBank,
    UwaResult& uwa
    ) const 
{
  CALL("Superposition::applyRule(Lhs const&, unsigned, Rhs const&, unsigned, UwaResult&)")
  MeasureTime time(env.statistics->ircSup);

  ASS (lhs.literal()->isEquality() && lhs.literal()->isPositive())
  auto s1 = lhs.biggerSide();
  auto s2 = rhs.toRewrite();
  auto nothing = [&]() {
    time.applicationCancelled();
    return Option<Clause*>();
  };
  ASS(!s1.isVar())
  ASS(!s2.isVar())

#define check_side_condition(cond, cond_code)                                                       \
    if (!(cond_code)) {                                                                             \
      DEBUG("side condition not fulfiled: ", cond)                                                  \
      return nothing();                                                                             \
    }                                                                                               \



  Stack<Literal*> concl(lhs.clause()->size() - 1 // <- C1σ
                      + rhs.clause()->size() - 1 // <- C2σ
                      + 1                        // <- L[s2]σ 
                      + uwa.cnst().size());      // <- Cnstσ




  auto L1σ = uwa.sigma(lhs.literal(), lhsVarBank);
  check_side_condition(
        "(s1 ≈ t)σ /⪯ C1σ",
        lhs.contextLiterals()
           .all([&](auto L) {
             auto Lσ = uwa.sigma(L, lhsVarBank);
             concl.push(Lσ);
             return OrderingUtils2::notLeq(_shared->ordering->compare(L1σ, Lσ));
           }))

  // •    L[s2]σ  ∈ Lit+ and L[s2]σ /⪯ C2σ
  //   or L[s2]σ /∈ Lit+ and L[s2]σ /≺ C2σ
  auto L2σ = uwa.sigma(rhs.literal(), rhsVarBank);
  bool inLitPlus = rhs.inLitPlus();
  check_side_condition(
      inLitPlus ? "L[s2]σ /⪯ C2σ"
                : "L[s2]σ /≺ C2σ",
        rhs.contextLiterals()
           .all([&](auto L) {
             auto Lσ = uwa.sigma(L, rhsVarBank);
             concl.push(Lσ);
             return inLitPlus ? OrderingUtils2::notLeq(_shared->ordering->compare(L2σ, Lσ))
                              : OrderingUtils2::notLess(_shared->ordering->compare(L2σ, Lσ));
           }));

  auto s2σ = uwa.sigma(s2, rhsVarBank);

  check_side_condition(
      "s2σ ⊴ ti ∈ active(L[s2]σ)", 
      _shared->activePositions(L2σ)
        .any([&](auto ti) 
             { return _shared->subtermEq(s2σ, ti); }))


  auto s1σ = uwa.sigma(lhs.biggerSide(), lhsVarBank);
  auto tσ  = uwa.sigma(lhs.smallerSide(), lhsVarBank);
  check_side_condition(
      "s1σ /⪯ tσ",
      OrderingUtils2::notLeq(_shared->ordering->compare(s1σ, tσ)))


  auto resolvent = EqHelper::replace(L2σ, s2σ, tσ);
  //   ^^^^^^^^^--> L[t]σ
  DEBUG("replacing: ", *L2σ, " [ ", s2σ, " -> ", tσ, " ] ==> ", *resolvent);
  concl.push(resolvent);

  // adding Cnst
  concl.loadFromIterator(uwa.cnstLiterals());

  Inference inf(GeneratingInference2(Kernel::InferenceRule::IRC_SUPERPOSITION, lhs.clause(), rhs.clause()));
  auto out = Clause::fromStack(concl, inf);
  DEBUG("out: ", *out);
  return Option<Clause*>(out);
}


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

// template<class NumTraits> auto Superposition::genRhs(Hyp2<NumTraits> hyp2) const 
// {
//   // ASS(hyp2.s2.isTerm())
//   // ASS_EQ(SortHelper::getResultSort(hyp2.s2.term()), NumTraits::sort())
//   // return iterTraits(pvi(this->_indexLhs->getUnificationsWithConstraints(hyp2.key(), true)))
//   //             .filterMap([=](TermQueryResult res) {
//   //               return applyRule<NumTraits>(
//   //                   Hyp1<NumTraits>::fromQueryResult(_shared, res), hyp2,
//   //                   res.substitution, res.constraints, 1);
//   //             });
// }

// template<class NumTraits> auto Superposition::genLhs(Hyp1<NumTraits> hyp1) const 
// {
//   // return iterTraits(pvi(this->_indexRhs->getUnificationsWithConstraints(hyp1.key(), true)))
//   //             .filterMap([=](TermQueryResult res) -> Option<Clause*> {
//   //
//   //               return applyRule<NumTraits>(
//   //                   hyp1, Hyp2<NumTraits>::fromQueryResult(_shared, res),
//   //                   res.substitution, res.constraints, 0);
//   //             });
// }

// auto Superposition::genRhs(IntTraits, Clause* premise, Lib::shared_ptr<Stack<Literal*>> const& maxLits)
// { return ClauseIterator::getEmpty(); }
//
// auto Superposition::genLhs(IntTraits, Clause* premise, Lib::shared_ptr<Stack<Literal*>> const& maxLits)
// { return ClauseIterator::getEmpty(); }

// template<class NumTraits> auto Superposition::genLhs(NumTraits numTraits, Clause* premise, Lib::shared_ptr<Stack<Literal*>> const& maxLits)
// {
//   // return iterHyp1Apps(_shared, numTraits, premise, maxLits)
//   //         .flatMap([&](auto hyp1) { return pvi(this->genLhs(hyp1)); });
// }

// template<class NumTraits> auto Superposition::genRhs(NumTraits numTraits, Clause* hyp2, Lib::shared_ptr<Stack<Literal*>> const& maxLits)
// {
//   // return iterHyp2Apps(_shared, numTraits, hyp2, maxLits)
//   //         .flatMap([&](auto hyp2) { return pvi(genRhs(hyp2)); });
// }

ClauseIterator Superposition::generateClauses(Clause* premise) 
{
  CALL("InequalityResolution::generateClauses(Clause* premise)")
  ASS(_lhs)
  ASS(_rhs)
  ASS(_shared)
  // TODO get rid of stack and unify with InequalityResolution
  Stack<Clause*> out;

  for (auto const& lhs : Lhs::iter(*_shared, premise)) {
    DEBUG("lhs: ", lhs)
    for (auto rhs_sigma : _rhs->find(lhs.key())) {
      auto& rhs = *std::get<0>(rhs_sigma);
      auto& sigma = std::get<1>(rhs_sigma);
      DEBUG("  rhs: ", rhs)
      auto res = applyRule(lhs, 0, rhs, 1, sigma);
      DEBUG("")
      if (res.isSome()) {
        out.push(res.unwrap());
      }
    }
  }

  for (auto const& rhs : Rhs::iter(*_shared, premise)) {
    DEBUG("rhs: ", rhs)
    for (auto lhs_sigma : _lhs->find(rhs.key())) {
      auto& lhs = *std::get<0>(lhs_sigma);
      auto& sigma = std::get<1>(lhs_sigma);
      DEBUG("  lhs: ", lhs)
      auto res = applyRule(lhs, 1, rhs, 0, sigma);
      DEBUG("")
      if (res.isSome()) {
        out.push(res.unwrap());
      }
    }
  }
  return pvi(ownedArrayishIterator(std::move(out)));
}

// TODO move to appropriate place

SimplifyingGeneratingInference::ClauseGenerationResult InequalityTautologyDetection::generateSimplify(Clause* premise) {
  Map<AnyIrcLiteral, bool, StlHash> lits;
    
  for (auto lit : iterTraits(premise->iterLits())) {
    auto norm_ = _shared->renormalize(lit);
    if (norm_.isSome()) {
      auto norm = norm_.unwrap();
      lits.insert(norm, true);
      auto opposite = norm.apply([&](auto lit) { return AnyIrcLiteral(lit.negation()); });
      if (lits.find(opposite)) {
        // std::cout << "bla" << std::endl;
        return ClauseGenerationResult {
          .clauses = ClauseIterator::getEmpty(),
          .premiseRedundant = true,
        };
      }
    }
  }

  return ClauseGenerationResult {
      .clauses = ClauseIterator::getEmpty(),
      .premiseRedundant = false,
    };
}


} // namespace IRC 
} // namespace Inferences 

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
#include "Indexing/SubstitutionTree.hpp"
#include "Lib/Metaiterators.hpp"
#include "Saturation/SaturationAlgorithm.hpp"
#include "Shell/Statistics.hpp"
#include "Debug/TimeProfiling.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/OrderingUtils.hpp"
#include "Kernel/LASCA.hpp"

#define DEBUG(lvl, ...) if (lvl < 0) DBG(__VA_ARGS__)

namespace Inferences {
namespace LASCA {

void Superposition::attach(SaturationAlgorithm* salg) 
{ 
  ASS(!_rhs);
  ASS(!_lhs);

  GeneratingInferenceEngine::attach(salg);

  _lhs=static_cast<decltype(_lhs)> (_salg->getIndexManager()
      ->request(LASCA_SUPERPOSITION_LHS_SUBST_TREE) );
  _lhs->setShared(_shared);

  _rhs=static_cast<decltype(_rhs)>(_salg->getIndexManager()
      ->request(LASCA_SUPERPOSITION_RHS_SUBST_TREE));
  _rhs->setShared(_shared);

}

void Superposition::detach() 
{
  ASS(_salg);

  _lhs=0;
  _salg->getIndexManager()->release(LASCA_SUPERPOSITION_LHS_SUBST_TREE);
  _rhs=0;
  _salg->getIndexManager()->release(LASCA_SUPERPOSITION_RHS_SUBST_TREE);
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
    AbstractingUnifier& uwa
    ) const 
{
  TIME_TRACE("lasca superposition application")

  ASS (lhs.literal()->isEquality() && lhs.literal()->isPositive())
#if VDEBUG
  auto s1 = lhs.biggerSide();
#endif
  auto s2 = rhs.toRewrite();
  auto nothing = [&]() { return Option<Clause*>(); };
  ASS(!(s1.isVar() && lhs.isFracNum()))
  ASS(!s2.isVar())

  auto cnst = uwa.computeConstraintLiterals();
  auto sigma = [&](auto t, auto bank) { return uwa.subs().apply(t, bank); };

#define check_side_condition(cond, cond_code)                                                       \
    if (!(cond_code)) {                                                                             \
      DEBUG(2, "side condition not fulfiled: ", cond)                                                  \
      return nothing();                                                                             \
    }                                                                                               \



  Stack<Literal*> concl(lhs.clause()->size() - 1 // <- C1σ
                      + rhs.clause()->size() - 1 // <- C2σ
                      + 1                        // <- L[s2]σ 
                      + cnst->size());      // <- Cnstσ


  auto unifySorts = [](auto s1, auto s2) -> Option<TermList> {
    static RobSubstitution subst;
    if (!subst.unify(s1, 0, s2, 0)) {
      return Option<TermList>();
    } else {
      ASS_EQ(subst.apply(s1,0), subst.apply(s2,0))
      return Option<TermList>(subst.apply(s1, 0));
    }
  };

  check_side_condition(
      "s1 and s2 are of unifyable sorts", 
      unifySorts(
        SortHelper::getEqualityArgumentSort(lhs.literal()), 
        SortHelper::getResultSort(s2.term())
        ).isSome()
      )

  auto L1σ = sigma(lhs.literal(), lhsVarBank);
  check_side_condition(
        "(s1 ≈ t)σ /⪯ C1σ",
        lhs.contextLiterals()
           .all([&](auto L) {
             auto Lσ = sigma(L, lhsVarBank);
             concl.push(Lσ);
             return _shared->notLeq(L1σ, Lσ);
           }))

  auto s2σ = sigma(s2, rhsVarBank);
  auto tσ  = sigma(lhs.smallerSide(), lhsVarBank);

  // •    L[s2]σ  ∈ Lit+ and L[s2]σ /⪯ C2σ
  //   or L[s2]σ /∈ Lit+ and L[s2]σ /≺ C2σ
  auto L2σ = sigma(rhs.literal(), rhsVarBank);
  bool inLitPlus = rhs.inLitPlus();
  check_side_condition(
      inLitPlus ? "L[s2]σ /⪯ C2σ"
                : "L[s2]σ /≺ C2σ",
        rhs.contextLiterals()
           .all([&](auto L) {
             auto Lσ = sigma(L, rhsVarBank);
             if (_simultaneousSuperposition) {
               concl.push(EqHelper::replace(Lσ, s2σ, tσ));
             } else {
               concl.push(Lσ);
             }
             return inLitPlus ? _shared->notLeq(L2σ, Lσ)
                              : _shared->notLess(L2σ, Lσ);
           }));

  check_side_condition(
      "s2σ ⊴ ti ∈ active(L[s2]σ)", 
      _shared->activePositions(L2σ)
        .any([&](auto ti) 
             { return _shared->subtermEq(s2σ, ti); }))

  check_side_condition(
      "L[s2]σ /⪯ L1σ", // TODO is this the correct thing? if so make sure we do that for fourrier motzkin and friends as well
      _shared->notLeq(L2σ, L1σ))


  auto s1σ = sigma(lhs.biggerSide() , lhsVarBank);
  check_side_condition(
      "s1σ /⪯ tσ",
      _shared->notLeq(s1σ.untyped(), tσ))


  auto resolvent = EqHelper::replace(L2σ, s2σ, tσ);
  //   ^^^^^^^^^--> L[t]σ
  DEBUG(3, "replacing: ", *L2σ, " [ ", s2σ, " -> ", tσ, " ] ==> ", *resolvent);
  concl.push(resolvent);

  // adding Cnst
  concl.loadFromIterator(cnst->iterFifo());

  Inference inf(GeneratingInference2(Kernel::InferenceRule::LASCA_SUPERPOSITION, lhs.clause(), rhs.clause()));
  auto out = Clause::fromStack(concl, inf);
  DEBUG(1, "out: ", *out);
  return Option<Clause*>(out);
}


ClauseIterator Superposition::generateClauses(Clause* premise) 
{
  ASS(_lhs)
  ASS(_rhs)
  ASS(_shared)
  // TODO get rid of stack and unify with FourierMotzkin
  Stack<Clause*> out;

  for (auto const& lhs : Lhs::iter(*_shared, premise)) {
    DEBUG(1, "lhs: ", lhs)
    for (auto rhs_sigma : _rhs->find(lhs.key())) {
      auto& rhs   = *rhs_sigma.data;
      auto& sigma = rhs_sigma.unifier;
      DEBUG(1, "  rhs: ", rhs)
      auto res = applyRule(lhs, QUERY_BANK, rhs, RESULT_BANK, *sigma);
      DEBUG(1, "")
      if (res.isSome()) {
        out.push(res.unwrap());
      }
    }
  }

  for (auto const& rhs : Rhs::iter(*_shared, premise)) {
    DEBUG(1, "rhs: ", rhs)
    for (auto lhs_sigma : _lhs->find(rhs.key())) {
      auto& lhs   = *lhs_sigma.data;
      auto& sigma = lhs_sigma.unifier;
      if (lhs.clause() != premise) { // <- self application. the same one has been run already in the previous loop
        DEBUG(1, "  lhs: ", lhs)
        auto res = applyRule(lhs, RESULT_BANK, rhs, QUERY_BANK, *sigma);
        DEBUG(1, "")
        if (res.isSome()) {
          out.push(res.unwrap());
        }
      }
    }
  }
  return pvi(arrayIter(std::move(out)));
}

// TODO move to appropriate place

SimplifyingGeneratingInference::ClauseGenerationResult InequalityTautologyDetection::generateSimplify(Clause* premise) {
  Map<AnyLascaLiteral, bool, StlHash> lits;
  TIME_TRACE("lasca tautology detection")
  for (auto lit : iterTraits(premise->iterLits())) {
    auto norm_ = _shared->renormalize(lit);
    if (norm_.isSome()) {
      auto norm = norm_.unwrap();
      lits.insert(norm, true);
      auto opposite = norm.apply([&](auto lit) { return AnyLascaLiteral(lit.negation()); });
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


} // namespace LASCA 
} // namespace Inferences 

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
 * @file UpwardChainBuilding.cpp
 * Implements class UpwardChainBuilding.
 */

#include "Lib/Metaiterators.hpp"

#include "Kernel/RobSubstitution.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/TermIterators.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"

#include "InductionRewriting.hpp"
#include "UpwardChainBuilding.hpp"

namespace Inferences {

using namespace Lib;
using namespace Kernel;

// inference

void UpwardChainBuilding::attach(SaturationAlgorithm* salg)
{
  GeneratingInferenceEngine::attach(salg);
  _lhsIndex=static_cast<TermIndex*>(
	  _salg->getIndexManager()->request(UNIT_LHS_INDEX) );
  _subtermIndex=static_cast<TermIndex*>(
	  _salg->getIndexManager()->request(UPWARD_CHAIN_BUILDING_SUBTERM_INDEX) );
}

void UpwardChainBuilding::detach()
{
  _lhsIndex = 0;
  _subtermIndex = 0;
  _salg->getIndexManager()->release(UNIT_LHS_INDEX);
  _salg->getIndexManager()->release(UPWARD_CHAIN_BUILDING_SUBTERM_INDEX);
  GeneratingInferenceEngine::detach();
}

ClauseIterator UpwardChainBuilding::generateClauses(Clause* premise)
{
  auto res = ClauseIterator::getEmpty();
  ASS(_salg->getOptions().introduceChains());

  if (premise->length()!=1) {
    return res;
  }
  auto lit = (*premise)[0];
  // cout << "lit " << *lit << endl;
  if (!lit->isEquality() || lit->isNegative()) {
    return res;
  }

  // 1. rewrite s[r]=t into s[l]=t with l=r where s[r] does not contain induction terms and l does

  // forward
  res = pvi(getConcatenatedIterator(res, pvi(iterTraits(lhsIterator(lit))
    .filter([](TypedTermList lhs) {
      return lhs.isTerm() && shouldChain(lhs.term());
    })
    .flatMap([](TypedTermList lhs) {
      return pvi(pushPairIntoRightIterator(lhs.term(), vi(new PositionalNonVariableNonTypeIterator(lhs.term()))));
    })
    .flatMap([this](pair<Term*,pair<Term*,Position>> arg) {
      return pvi(pushPairIntoRightIterator(arg, _lhsIndex->getUnifications(arg.second.first, true)));
    })
    .filter([](pair<pair<Term*,pair<Term*,Position>>,TermQueryResult> arg) {
      auto qr = arg.second;
      auto eqRhs = EqHelper::getOtherEqualitySide(qr.literal, qr.term);
      return eqRhs.isTerm() && !shouldChain(eqRhs.term());
    })
    .map([lit,premise,this](pair<pair<Term*,pair<Term*,Position>>,TermQueryResult> arg) -> Clause* {
      auto side = arg.first.first;
      auto rwTerm = arg.first.second.first;
      auto pos = arg.first.second.second;
      auto qr = arg.second;
      return perform(premise,lit,TermList(side),TermList(rwTerm),qr.clause,qr.literal,qr.term,pos,qr.substitution,true,true);
    }))));

  // backward
  res = pvi(getConcatenatedIterator(res, pvi(iterTraits(lhsIterator(lit))
    .filter([lit](TypedTermList lhs) {
      auto rhs = EqHelper::getOtherEqualitySide(lit, lhs);
      return rhs.isTerm() && !shouldChain(rhs.term());
    })
    .flatMap([this](TypedTermList lhs) {
      return pvi(pushPairIntoRightIterator(lhs,_subtermIndex->getUnifications(lhs, true)));
    })
    .flatMap([](pair<TypedTermList,TermQueryResult> arg) {
      auto t = arg.second.term.term();
      auto t0 = arg.second.literal->termArg(0);
      auto t1 = arg.second.literal->termArg(1);
      return pushPairIntoRightIterator(arg,
        pvi(getConcatenatedIterator(
          pvi(pushPairIntoRightIterator(t0,getPositions(t0,t))),
          pvi(pushPairIntoRightIterator(t1,getPositions(t1,t)))
        )));
    })
    .filter([](pair<pair<TypedTermList,TermQueryResult>,pair<TermList,pair<Term*,Position>>> arg) {
      auto side = arg.second.first;
      return side.isTerm() && shouldChain(side.term());
    })
    .map([lit,premise,this](pair<pair<TypedTermList,TermQueryResult>,pair<TermList,pair<Term*,Position>>> arg) -> Clause* {
      auto eqLHS = arg.first.first;
      auto side = arg.second.first;
      auto rwTerm = arg.first.second.term;
      ASS_EQ(arg.second.second.first,rwTerm.term());
      auto pos = arg.second.second.second;
      auto qr = arg.first.second;
      return perform(qr.clause,qr.literal,side,rwTerm,premise,lit,eqLHS,pos,qr.substitution,false,true);
    }))));

  // 2. rewrite s=t[l] into s=t[r] with l=r where l does not contain induction terms and s does

  // forward
  res = pvi(getConcatenatedIterator(res, pvi(iterTraits(lhsIterator(lit))
    .filter([lit](TypedTermList lhs) {
      auto rhs = EqHelper::getOtherEqualitySide(lit,lhs);
      return lhs.isTerm() && rhs.isTerm() && !shouldChain(rhs.term());
    })
    .flatMap([](TypedTermList lhs) {
      return pvi(pushPairIntoRightIterator(lhs.term(), vi(new PositionalNonVariableNonTypeIterator(lhs.term()))));
    })
    .flatMap([this](pair<Term*,pair<Term*,Position>> arg) {
      return pvi(pushPairIntoRightIterator(arg,_lhsIndex->getUnifications(arg.second.first, true)));
    })
    .filter([](pair<pair<Term*,pair<Term*,Position>>,TermQueryResult> arg) {
      auto qr = arg.second;
      return qr.term.isTerm() && shouldChain(qr.term.term());
    })
    .map([lit,premise,this](pair<pair<Term*,pair<Term*,Position>>,TermQueryResult> arg) -> Clause* {
      auto side = arg.first.first;
      auto rwTerm = arg.first.second.first;
      auto pos = arg.first.second.second;
      auto qr = arg.second;
      return perform(premise,lit,TermList(side),TermList(rwTerm),qr.clause,qr.literal,qr.term,pos,qr.substitution,true,false);
    }))));

  // backward
  res = pvi(getConcatenatedIterator(res, pvi(iterTraits(lhsIterator(lit))
    .filter([](TypedTermList lhs) {
      return lhs.isTerm() && shouldChain(lhs.term());
    })
    .flatMap([this](TypedTermList lhs) {
      return pvi(pushPairIntoRightIterator(lhs.term(),_subtermIndex->getUnifications(lhs.term(), true)));
    })
    .flatMap([](pair<Term*,TermQueryResult> arg) {
      auto t = arg.second.term.term();
      auto t0 = arg.second.literal->termArg(0);
      auto t1 = arg.second.literal->termArg(1);
      return pushPairIntoRightIterator(arg,
        pvi(getConcatenatedIterator(
          pvi(pushPairIntoRightIterator(t0,getPositions(t0,t))),
          pvi(pushPairIntoRightIterator(t1,getPositions(t1,t)))
        )));
    })
    .filter([](pair<pair<Term*,TermQueryResult>,pair<TermList,pair<Term*,Position>>> arg) {
      auto side = arg.second.first;
      auto other = EqHelper::getOtherEqualitySide(arg.first.second.literal,side);
      return side.isTerm() && other.isTerm() && !shouldChain(other.term());
    })
    .map([lit,premise,this](pair<pair<Term*,TermQueryResult>,pair<TermList,pair<Term*,Position>>> arg) -> Clause* {
      auto eqLHS = TermList(arg.first.first);
      auto side = arg.second.first;
      auto rwTerm = arg.first.second.term;
      ASS_EQ(arg.second.second.first,rwTerm.term());
      auto pos = arg.second.second.second;
      auto qr = arg.first.second;
      return perform(qr.clause,qr.literal,side,rwTerm,premise,lit,eqLHS,pos,qr.substitution,false,false);
    }))));
  return pvi(iterTraits(res)
    .filter(NonzeroFn())
    .timeTraced("upward chain building"));
}

Clause* UpwardChainBuilding::perform(
    Clause* rwClause, Literal* rwLit, TermList rwSide, TermList rwTerm,
    Clause* eqClause, Literal* eqLit, TermList eqLHS, const Position& pos,
    ResultSubstitutionSP subst, bool eqIsResult, bool left)
{
  TIME_TRACE("perform upward chain building");
  // we want the rwClause and eqClause to be active
  ASS(rwClause->store()==Clause::ACTIVE);
  ASS(eqClause->store()==Clause::ACTIVE);
  ASS_EQ(rwClause->length(),1);
  ASS_EQ(eqClause->length(),1);
  ASS(rwLit->isEquality()&&rwLit->isPositive());
  ASS(eqLit->isEquality()&&eqLit->isPositive());

  if (rwClause->remDepth()+eqClause->remDepth()>=_salg->getOptions().maxRemodulationDepth()) {
    return 0;
  }

  TermList tgtTerm = EqHelper::getOtherEqualitySide(eqLit, eqLHS);
  Ordering& ordering = _salg->getOrdering();

  TermList tgtTermS = subst->apply(tgtTerm, eqIsResult);

  TermList rwTermS = subst->apply(rwTerm, !eqIsResult);
  TermList rwSideS = subst->apply(rwSide, !eqIsResult);
  TermList otherSide = EqHelper::getOtherEqualitySide(rwLit, rwSide);
  TermList otherSideS = subst->apply(otherSide, !eqIsResult);

  if (left) {
    // we rewrite the not-smaller side into a not-smaller term
    if (Ordering::isGorGEorE(ordering.compare(rwTermS,tgtTermS))) {
      return 0;
    }
    if (Ordering::isGorGEorE(ordering.compare(otherSideS,rwSideS))) {
      return 0;
    }
  } else {
    // we rewrite the not-greater side into a not-greater term 
    if (Ordering::isGorGEorE(ordering.compare(tgtTermS,rwTermS))) {
      return 0;
    }
    if (Ordering::isGorGEorE(ordering.compare(rwSideS,otherSideS))) {
      return 0;
    }
  }

  ASS(rwSideS.isTerm());
  auto tgtSideS = replaceOccurrence(rwSideS.term(),rwTermS.term(),tgtTermS,pos);
  Literal* rwLitS = subst->apply(rwLit, !eqIsResult);
  Literal* tgtLitS = Literal::createEquality(true, tgtSideS, otherSideS, SortHelper::getEqualityArgumentSort(rwLitS));

  if(EqHelper::isEqTautology(tgtLitS)) {
    return 0;
  }

  Inference inf(GeneratingInference2(InferenceRule::UPWARD_CHAIN_BUILDING, rwClause, eqClause));
  Clause* res = new(1) Clause(1, inf);
  (*res)[0] = tgtLitS;
  // cout << (eqIsResult ? "forward " : "backward ") << "chain " << *res << endl
  //      << "from " << *rwClause << endl
  //      << "and " << *eqClause << endl << endl;
  // cout << left << " " << eqIsResult << endl;
  res->setRemDepth(rwClause->remDepth()+eqClause->remDepth()+1);
  env.statistics->upwardChainBuilding++;
  return res;
}

}
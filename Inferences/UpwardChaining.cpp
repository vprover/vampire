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
 * @file UpwardChaining.cpp
 * Implements class UpwardChaining.
 */

#include "Lib/Metaiterators.hpp"

#include "Kernel/RobSubstitution.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/TermIterators.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"

#include "InductionRewriting.hpp"
#include "UpwardChaining.hpp"

namespace Inferences {

using namespace Lib;
using namespace Kernel;

// inference

void UpwardChaining::attach(SaturationAlgorithm* salg)
{
  GeneratingInferenceEngine::attach(salg);
  _leftLhsIndex=static_cast<TermIndex*>(
	  _salg->getIndexManager()->request(LEFT_UPWARD_CHAINING_LHS_INDEX) );
  _rightLhsIndex=static_cast<TermIndex*>(
	  _salg->getIndexManager()->request(RIGHT_UPWARD_CHAINING_LHS_INDEX) );
  _leftSubtermIndex=static_cast<TermIndex*>(
	  _salg->getIndexManager()->request(LEFT_UPWARD_CHAINING_SUBTERM_INDEX) );
  _rightSubtermIndex=static_cast<TermIndex*>(
	  _salg->getIndexManager()->request(RIGHT_UPWARD_CHAINING_SUBTERM_INDEX) );
}

void UpwardChaining::detach()
{
  _leftLhsIndex = 0;
  _rightLhsIndex = 0;
  _leftSubtermIndex = 0;
  _rightSubtermIndex = 0;
  _salg->getIndexManager()->release(LEFT_UPWARD_CHAINING_LHS_INDEX);
  _salg->getIndexManager()->release(RIGHT_UPWARD_CHAINING_LHS_INDEX);
  _salg->getIndexManager()->release(LEFT_UPWARD_CHAINING_SUBTERM_INDEX);
  _salg->getIndexManager()->release(RIGHT_UPWARD_CHAINING_SUBTERM_INDEX);
  GeneratingInferenceEngine::detach();
}

ClauseIterator UpwardChaining::generateClauses(Clause* premise)
{
  auto res = ClauseIterator::getEmpty();
  ASS(_salg->getOptions().goalParamodulationChaining());

  if (premise->length()!=1) {
    return res;
  }

  auto lit = (*premise)[0];
  if (!lit->isEquality() || lit->isNegative()) {
    return res;
  }

  if (premise->remDepth()>=_salg->getOptions().maxGoalParamodulationDepth()) {
    return res;
  }

  const auto& ord = _salg->getOrdering();

  // left
  // 1. rewrite s[r]=t into s[l]=t with l=r where s[r] does not contain induction terms and l does

  // forward
  res = pvi(getConcatenatedIterator(res, pvi(iterTraits(orderedLhsIterator(lit, ord, false /*reverse*/))
    .filter([](TypedTermList lhs) {
      return lhs.isTerm() && shouldChain(lhs.term());
    })
    .flatMap([](TypedTermList lhs) {
      return pvi(pushPairIntoRightIterator(lhs.term(), vi(new PositionalNonVariableNonTypeIterator(lhs.term()))));
    })
    .flatMap([this](pair<Term*,pair<Term*,Position>> arg) {
      return pvi(pushPairIntoRightIterator(arg, _leftLhsIndex->getUnifications(arg.second.first, true)));
    })
    .map([lit,premise,this](pair<pair<Term*,pair<Term*,Position>>,TermQueryResult> arg) -> Clause* {
      auto side = arg.first.first;
      auto rwTerm = arg.first.second.first;
      auto pos = arg.first.second.second;
      auto qr = arg.second;
      ASS(!shouldChain(EqHelper::getOtherEqualitySide(qr.literal, qr.term).term()));
      return perform(premise,lit,TermList(side),TermList(rwTerm),qr.clause,qr.literal,qr.term,pos,qr.substitution,true,true);
    }))));

  // backward
  res = pvi(getConcatenatedIterator(res, pvi(iterTraits(orderedLhsIterator(lit, ord, true /*reverse*/))
    .filter([lit](TypedTermList lhs) {
      auto rhs = EqHelper::getOtherEqualitySide(lit, lhs);
      return rhs.isTerm() && !shouldChain(rhs.term());
    })
    .flatMap([this](TypedTermList lhs) {
      return pvi(pushPairIntoRightIterator(lhs,_leftSubtermIndex->getUnifications(lhs, true)));
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

  // right
  // 2. rewrite s=t[l] into s=t[r] with l=r where l does not contain induction terms and s does

  // forward
  res = pvi(getConcatenatedIterator(res, pvi(iterTraits(orderedLhsIterator(lit, ord, true /*reverse*/))
    .filter([lit](TypedTermList lhs) {
      auto rhs = EqHelper::getOtherEqualitySide(lit,lhs);
      return lhs.isTerm() && rhs.isTerm() && !shouldChain(rhs.term());
    })
    .flatMap([](TypedTermList lhs) {
      return pvi(pushPairIntoRightIterator(lhs.term(), vi(new PositionalNonVariableNonTypeIterator(lhs.term()))));
    })
    .flatMap([this](pair<Term*,pair<Term*,Position>> arg) {
      return pvi(pushPairIntoRightIterator(arg,_rightLhsIndex->getUnifications(arg.second.first, true)));
    })
    .map([lit,premise,this](pair<pair<Term*,pair<Term*,Position>>,TermQueryResult> arg) -> Clause* {
      auto side = arg.first.first;
      auto rwTerm = arg.first.second.first;
      auto pos = arg.first.second.second;
      auto qr = arg.second;
      ASS(shouldChain(qr.term.term()));
      return perform(premise,lit,TermList(side),TermList(rwTerm),qr.clause,qr.literal,qr.term,pos,qr.substitution,true,false);
    }))));

  // backward
  res = pvi(getConcatenatedIterator(res, pvi(iterTraits(orderedLhsIterator(lit, ord, false /*reverse*/))
    .filter([](TypedTermList lhs) {
      return lhs.isTerm() && shouldChain(lhs.term());
    })
    .flatMap([this](TypedTermList lhs) {
      return pvi(pushPairIntoRightIterator(lhs.term(),_rightSubtermIndex->getUnifications(lhs.term(), true)));
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
    .timeTraced("upward chaining"));
}

Clause* UpwardChaining::perform(
    Clause* rwClause, Literal* rwLit, TermList rwSide, TermList rwTerm,
    Clause* eqClause, Literal* eqLit, TermList eqLHS, const Position& pos,
    ResultSubstitutionSP subst, bool eqIsResult, bool left)
{
  // we want the rwClause and eqClause to be active
  ASS(rwClause->store()==Clause::ACTIVE);
  ASS(eqClause->store()==Clause::ACTIVE);
  ASS_EQ(rwClause->length(),1);
  ASS_EQ(eqClause->length(),1);
  ASS(rwLit->isEquality()&&rwLit->isPositive());
  ASS(eqLit->isEquality()&&eqLit->isPositive());

  if (rwClause->remDepth()+eqClause->remDepth()>=_salg->getOptions().maxGoalParamodulationDepth()) {
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

  Inference inf(GeneratingInference2(InferenceRule::UPWARD_CHAINING, rwClause, eqClause));
  Clause* res = new(1) Clause(1, inf);
  (*res)[0] = tgtLitS;
  // cout << (eqIsResult ? "forward " : "backward ") << "chain " << *res << endl
  //      << "from " << *rwClause << endl
  //      << "and " << *eqClause << endl << endl;
  // cout << left << " " << eqIsResult << endl;
  res->setRemDepth(rwClause->remDepth()+eqClause->remDepth()+1);
  env.statistics->goalParamodulationChaining++;
  return res;
}

}
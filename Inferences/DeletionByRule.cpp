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
 * @file DeletionByRule.cpp
 * Implements class DeletionByRule.
 */

#include "DeletionByRule.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/RewritingData.hpp"
#include "Kernel/VarOrder.hpp"
#include "Saturation/SaturationAlgorithm.hpp"

using namespace Kernel;
using namespace Inferences;

void ForwardDeletionByRule::attach(SaturationAlgorithm* salg)
{
  ForwardSimplificationEngine::attach(salg);
  _index=static_cast<DemodulationLHSIndex*>(
	  _salg->getIndexManager()->request(DEMODULATION_LHS_CODE_TREE) );
}

void ForwardDeletionByRule::detach()
{
  _index=nullptr;
  _salg->getIndexManager()->release(DEMODULATION_LHS_CODE_TREE);
  ForwardSimplificationEngine::detach();
}

bool ForwardDeletionByRule::perform(Clause* cl, Clause*& replacement, ClauseIterator& premises)
{
  TIME_TRACE("forward deletion by rule");
  auto& ord = _salg->getOrdering();
  auto rwData = cl->rewritingData();
  if (!rwData) {
    return false;
  }

#if CONDITIONAL_MODE
  ClauseStack condPrem;
  VarOrderBV bits = 0;
#endif
  auto it = rwData->iter();
  while (it.hasNext()) {
    Term* lhs;
    auto& info = it.nextRef(lhs);
    if (info.rhs.isNonEmpty()) {
      continue;
    }
    if (!rwData->validate(lhs,info)) {
      it.del();
      continue;
    }
#if CONDITIONAL_MODE
    {
      if (info.rhs.isNonEmpty()) {
        VarOrderBV bits2 = getRemaining(bits);
        if (ord.isGreater(info.rhs,TermList(lhs),nullptr,&bits2)) {
          TIME_TRACE("ordering check");
          return true;
        }
        if (bits2) {
          bits |= bits2;
        }
      }
    }
#endif
    TermQueryResultIterator git=_index->getGeneralizations(lhs, true);
    while(git.hasNext()) {
      TermQueryResult qr=git.next();
      auto qrRwData = qr.clause->rewritingData();
      if (qrRwData && !qrRwData->subsumes(rwData, [qr](TermList t) {
        ASS(qr.substitution->isIdentityOnQueryWhenResultBound());
        return qr.substitution->applyToBoundResult(t);
      }, lhs)) {
        continue;
      }

      TermList rhs=EqHelper::getOtherEqualitySide(qr.literal,qr.term);
#if CONDITIONAL_MODE
      VarOrderBV bits2 = getRemaining(bits);
      if (!ord.isGreater(TermList(lhs),rhs,nullptr,&bits2,&qr)) {
        if (!bits2 || info.rhs.isNonEmpty()) {
          continue;
        }
        bits |= bits2;
        condPrem.push(qr.clause);
        if (isReducedUnderAny(bits)) {
          premises = getUniquePersistentIterator(ClauseStack::Iterator(condPrem));
          env.statistics->forwardConditionalDeletionByRuleBlocked++;
          goto success;
        }
        continue;
      }
#else
      if (!ord.isGreater(TermList(lhs),rhs,nullptr,nullptr,&qr)) {
        continue;
      }
#endif
      premises = pvi(getSingletonIterator(qr.clause));
      if (info.rhs.isNonEmpty()) {
        auto rhsS = qr.substitution->applyToBoundResult(rhs);
#if CONDITIONAL_MODE
        VarOrderBV bits2 = getRemaining(bits);
        if (!ord.isGreater(info.rhs,rhsS,nullptr,&bits2)) {
          // if (!ord.isGreater(info.rhs,rhs,nullptr,nullptr,&qr)) {
          if (!bits2) {
            continue;
          }
          bits |= bits2;
          condPrem.push(qr.clause);
          if (isReducedUnderAny(bits)) {
            premises = getUniquePersistentIterator(ClauseStack::Iterator(condPrem));
            env.statistics->forwardConditionalDeletionByRule++;
            goto success;
          }
          continue;
        }
#else
        if (!ord.isGreater(info.rhs,rhsS)) {
          continue;
        }
#endif
        // std::cout << *lhs << " " << info.rhs << " " << rhs << " " << rhsS << std::endl;
        env.statistics->forwardDeletionByRule++;
      } else {
        env.statistics->forwardDeletionByRuleBlocked++;
      }
success:
      return true;
    }
  }
#if CONDITIONAL_MODE
  cl->reducedUnder() = bits;
#endif
  return false;
}

void BackwardDeletionByRule::attach(SaturationAlgorithm* salg)
{
  BackwardSimplificationEngine::attach(salg);
  _index=static_cast<BlockedTermIndex*>(
	  _salg->getIndexManager()->request(BLOCKED_TERM_INDEX) );
}

void BackwardDeletionByRule::detach()
{
  _index=0;
  _salg->getIndexManager()->release(BLOCKED_TERM_INDEX);
  BackwardSimplificationEngine::detach();
}

struct BackwardDeletionByRuleResultFn
{
  typedef DHMultiset<Clause*> ClauseSet;

  BackwardDeletionByRuleResultFn(Clause* cl, const Ordering& ord)
  : _cl(cl), _ordering(ord)
  {
    ASS_EQ(_cl->length(),1);
    _eqLit=(*_cl)[0];
    _removed=SmartPtr<ClauseSet>(new ClauseSet());
  }

  /**
   * Return pair of clauses. First clause is being replaced,
   * and the second is the clause, that replaces it. If no
   * replacement should occur, return pair of zeroes.
   */
  BwSimplificationRecord operator() (std::pair<TermList,TermQueryResult> arg)
  {
    TIME_TRACE("backward deletion by rule");

    TermQueryResult qr=arg.second;

    if(_cl==qr.clause || _removed->find(qr.clause)) {
      //the retreived clause was already replaced during this
      //backward demodulation
      return BwSimplificationRecord(nullptr);
    }

    TermList lhs=arg.first;

    // AYB there used to be a check here to ensure that the sorts
    // matched. This is no longer necessary, as sort matching / unification
    // is handled directly within the tree

    TermList rhs=EqHelper::getOtherEqualitySide(_eqLit, lhs);
    TermList lhsS=qr.term;
    TermList rhsS;

    if(!qr.substitution->isIdentityOnResultWhenQueryBound()) {
      //When we apply substitution to the rhs, we get a term, that is
      //a variant of the term we'd like to get, as new variables are
      //produced in the substitution application.
      //We'd rather rename variables in the rhs, than in the whole clause
      //that we're simplifying.
      TermList lhsSBadVars=qr.substitution->applyToQuery(lhs);
      TermList rhsSBadVars=qr.substitution->applyToQuery(rhs);
      Renaming rNorm, qNorm, qDenorm;
      rNorm.normalizeVariables(lhsSBadVars);
      qNorm.normalizeVariables(lhsS);
      qDenorm.makeInverse(qNorm);
      ASS_EQ(lhsS,qDenorm.apply(rNorm.apply(lhsSBadVars)));
      rhsS=qDenorm.apply(rNorm.apply(rhsSBadVars));
    } else {
      rhsS=qr.substitution->applyToBoundQuery(rhs);
    }

    if(!_ordering.isGreater(lhsS,rhsS)) {
      return BwSimplificationRecord(nullptr);
    }

    ASS(qr.clause->rewritingData()->isBlocked(lhsS.term()));

    auto rwData = _cl->rewritingData();
    if (!rwData || rwData->subsumes(qr.clause->rewritingData(), [qr](TermList t) {
      ASS(qr.substitution->isIdentityOnResultWhenQueryBound());
      return qr.substitution->applyToBoundQuery(t);
    }, lhsS.term())) {
      TIME_TRACE("backward deletion by rule success");
      _removed->insert(qr.clause);
      return BwSimplificationRecord(qr.clause);
    }

    return BwSimplificationRecord(nullptr);
  }
private:
  TermList _eqSort;
  Literal* _eqLit;
  Clause* _cl;
  SmartPtr<ClauseSet> _removed;

  const Ordering& _ordering;
};

void BackwardDeletionByRule::perform(Clause* cl, BwSimplificationRecordIterator& simplifications)
{
  TIME_TRACE("backward deletion by rule");

  if(cl->length()!=1 || !(*cl)[0]->isEquality() || !(*cl)[0]->isPositive() ) {
    simplifications=BwSimplificationRecordIterator::getEmpty();
    return;
  }
  Literal* lit=(*cl)[0];

  BwSimplificationRecordIterator replacementIterator=
    pvi( getFilteredIterator(
      getMappingIterator(
        getMapAndFlattenIterator(
          EqHelper::getDemodulationLHSIterator(lit, false, _salg->getOrdering(), _salg->getOptions()),
          [this](TypedTermList lhs) { return pvi( pushPairIntoRightIterator(lhs, _index->getInstances(lhs, true)) ); }),
      BackwardDeletionByRuleResultFn(cl, _salg->getOrdering())),
    [](BwSimplificationRecord arg) { return arg.toRemove!=0; }) );

  //here we know that the getPersistentIterator evaluates all items of the
  //replacementIterator right at this point, so we can measure the time just
  //simply (which cannot be generally done when iterators are involved)

  simplifications=getPersistentIterator(replacementIterator);
}

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
 * @file BackwardDemodulation.cpp
 * Implements class SLQueryBackwardSubsumption.
 */


#include "Lib/DHMultiset.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/List.hpp"
#include "Lib/Metaiterators.hpp"
#include "Debug/TimeProfiling.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/ColorHelper.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/Renaming.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/RobSubstitution.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/TermIndex.hpp"
#include "Indexing/IndexManager.hpp"
#include "Debug/TimeProfiling.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "BackwardDemodulation.hpp"

namespace Inferences {

using namespace std;
using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

void BackwardDemodulation::attach(SaturationAlgorithm* salg)
{
  BackwardSimplificationEngine::attach(salg);
  _index=static_cast<DemodulationSubtermIndex*>(
	  _salg->getIndexManager()->request(DEMODULATION_SUBTERM_SUBST_TREE) );
}

void BackwardDemodulation::detach()
{
  _index=0;
  _salg->getIndexManager()->release(DEMODULATION_SUBTERM_SUBST_TREE);
  BackwardSimplificationEngine::detach();
}

struct BackwardDemodulation::RemovedIsNonzeroFn
{
  bool operator() (BwSimplificationRecord arg)
  {
    return arg.toRemove!=0;
  }
};

struct BackwardDemodulation::RewritableClausesFn
{
  RewritableClausesFn(DemodulationSubtermIndex* index) : _index(index) {}
  VirtualIterator<pair<TypedTermList,TermQueryResult> > operator() (TypedTermList lhs)
  {
    return pvi( pushPairIntoRightIterator(lhs, _index->getInstances(lhs, true)) );
  }
private:
  DemodulationSubtermIndex* _index;
};


struct BackwardDemodulation::ResultFn
{
  typedef DHMultiset<Clause*> ClauseSet;

  ResultFn(Clause* cl, BackwardDemodulation& parent)
  : _cl(cl), _ordering(parent._salg->getOrdering())
  {
    ASS_EQ(_cl->length(),1);
    _eqLit=(*_cl)[0];
    _eqSort = SortHelper::getEqualityArgumentSort(_eqLit);
    _removed=SmartPtr<ClauseSet>(new ClauseSet());
    _preorderedOnly = parent.getOptions().backwardDemodulation() == Options::Demodulation::PREORDERED;
    _redundancyCheck = parent.getOptions().demodulationRedundancyCheck() != Options::DemodulationRedundancyCheck::OFF;
    _encompassing = parent.getOptions().demodulationRedundancyCheck() == Options::DemodulationRedundancyCheck::ENCOMPASS;
    _precompiledComparison = parent.getOptions().demodulationPrecompiledComparison();
  }

  /**
   * Return pair of clauses. First clause is being replaced,
   * and the second is the clause, that replaces it. If no
   * replacement should occur, return pair of zeroes.
   */
  BwSimplificationRecord operator() (pair<TermList,TermQueryResult> arg)
  {
    TermQueryResult qr=arg.second;

    if( !ColorHelper::compatible(_cl->color(), qr.clause->color()) ) {
      //colors of premises don't match
      return BwSimplificationRecord(0);
    }

    if(_cl==qr.clause || _removed->find(qr.clause)) {
      //the retreived clause was already replaced during this
      //backward demodulation
      return BwSimplificationRecord(0);
    }

    TermList lhs=arg.first;
    TermList rhs=EqHelper::getOtherEqualitySide(_eqLit, lhs);

    // AYB there used to be a check here to ensure that the sorts
    // matched. This is no longer necessary, as sort matching / unification
    // is handled directly within the tree

    Ordering::Result argOrder = _ordering.getEqualityArgumentOrder(_eqLit);
    bool preordered = argOrder==Ordering::LESS || argOrder==Ordering::GREATER;
#if VDEBUG
    if(preordered) {
      if(argOrder==Ordering::LESS) {
        ASS_EQ(rhs, *_eqLit->nthArgument(0));
      }
      else {
        ASS_EQ(rhs, *_eqLit->nthArgument(1));
      }
    }
#endif

    auto subs = qr.unifier;
    ASS(subs->isIdentityOnResultWhenQueryBound());

    if (_precompiledComparison) {
      if (!preordered && (_preorderedOnly || !_ordering.isGreater(_eqLit,lhs,subs.ptr(),false/*result*/))) {
        return BwSimplificationRecord(0);
      }
    }

    TermList lhsS=qr.term;
    TermList rhsS=subs->applyToBoundQuery(rhs);

    if (!_precompiledComparison) {
      if (!preordered && (_preorderedOnly || _ordering.compare(lhsS,rhsS)!=Ordering::GREATER)) {
        return BwSimplificationRecord(0);
      }
    }

    if(_redundancyCheck && qr.literal->isEquality() && (qr.term==*qr.literal->nthArgument(0) || qr.term==*qr.literal->nthArgument(1)) &&
      // encompassment has issues only with positive units
      (!_encompassing || (qr.literal->isPositive() && qr.clause->length() == 1))) {
      TermList other=EqHelper::getOtherEqualitySide(qr.literal, qr.term);
      Ordering::Result tord=_ordering.compare(rhsS, other);
      if(tord!=Ordering::LESS && tord!=Ordering::LESS_EQ) {
        if (_encompassing) {
          if (subs->isRenamingOn(lhs,false /* we talk of a non-result, i.e., a query term */)) {
            // under _encompassing, we know there are no other literals in qr.clause
            return BwSimplificationRecord(0);
          }
        } else {
          TermList eqSort = SortHelper::getEqualityArgumentSort(qr.literal);
          Literal* eqLitS=Literal::createEquality(true, lhsS, rhsS, eqSort);
          bool isMax=true;
          for (Literal* lit2 : qr.clause->iterLits()) {
            if(qr.literal==lit2) {
              continue;
            }
            if(_ordering.compare(eqLitS, lit2)==Ordering::LESS) {
              isMax=false;
              break;
            }
          }
          if(isMax) {
            //	  RSTAT_CTR_INC("bw subsumptions prevented by tlCheck");
            //The demodulation is this case which doesn't preserve completeness:
            //s = t     s = t1 \/ C
            //---------------------
            //     t = t1 \/ C
            //where t > t1 and s = t > C
            return BwSimplificationRecord(0);
          }
        }
      }
    }

    Literal* resLit=EqHelper::replace(qr.literal,lhsS,rhsS);
    if(EqHelper::isEqTautology(resLit)) {
      env.statistics->backwardDemodulationsToEqTaut++;
      _removed->insert(qr.clause);
      return BwSimplificationRecord(qr.clause);
    }

    unsigned cLen=qr.clause->length();
    Clause* res = new(cLen) Clause(cLen, SimplifyingInference2(InferenceRule::BACKWARD_DEMODULATION, qr.clause, _cl));

    (*res)[0]=resLit;

    unsigned next=1;
    for(unsigned i=0;i<cLen;i++) {
      Literal* curr=(*qr.clause)[i];
      if(curr!=qr.literal) {
        (*res)[next++] = curr;
      }
    }
    ASS_EQ(next,cLen);

    env.statistics->backwardDemodulations++;
    _removed->insert(qr.clause);
    return BwSimplificationRecord(qr.clause,res);
  }
private:
  TermList _eqSort;
  Literal* _eqLit;
  Clause* _cl;
  SmartPtr<ClauseSet> _removed;

  bool _preorderedOnly;
  bool _redundancyCheck;
  bool _encompassing;
  bool _precompiledComparison;

  Ordering& _ordering;
};


void BackwardDemodulation::perform(Clause* cl,
	BwSimplificationRecordIterator& simplifications)
{
  TIME_TRACE("backward demodulation");

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
			    RewritableClausesFn(_index)),
		    ResultFn(cl, *this)),
 	    RemovedIsNonzeroFn()) );

  //here we know that the getPersistentIterator evaluates all items of the
  //replacementIterator right at this point, so we can measure the time just
  //simply (which cannot be generally done when iterators are involved)

  simplifications=getPersistentIterator(replacementIterator);
}

}

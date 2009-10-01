/**
 * @file BackwardDemodulation.cpp
 * Implements class SLQueryBackwardSubsumption.
 */


#include "../Lib/DHMultiset.hpp"
#include "../Lib/Environment.hpp"
#include "../Lib/Int.hpp"
#include "../Lib/List.hpp"
#include "../Lib/Metaiterators.hpp"
#include "../Lib/TimeCounter.hpp"
#include "../Lib/VirtualIterator.hpp"

#include "../Kernel/Term.hpp"
#include "../Kernel/Clause.hpp"
#include "../Kernel/EqHelper.hpp"
#include "../Kernel/Renaming.hpp"
#include "../Kernel/Ordering.hpp"
#include "../Kernel/Inference.hpp"

#include "../Indexing/Index.hpp"
#include "../Indexing/TermIndex.hpp"
#include "../Indexing/IndexManager.hpp"

#include "../Saturation/SaturationAlgorithm.hpp"

#include "../Shell/Statistics.hpp"

#include "BackwardDemodulation.hpp"

namespace Inferences {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

void BackwardDemodulation::attach(SaturationAlgorithm* salg)
{
  CALL("BackwardDemodulation::attach");
  BackwardSimplificationEngine::attach(salg);
  _index=static_cast<DemodulationSubtermIndex*>(
	  _salg->getIndexManager()->request(DEMODULATION_SUBTERM_SUBST_TREE) );
}

void BackwardDemodulation::detach()
{
  CALL("BackwardDemodulation::detach");
  _index=0;
  _salg->getIndexManager()->release(DEMODULATION_SUBTERM_SUBST_TREE);
  BackwardSimplificationEngine::detach();
}

struct BackwardDemodulation::RemovedIsNonzeroFn
{
  DECL_RETURN_TYPE(bool);
  OWN_RETURN_TYPE operator() (BwSimplificationRecord arg)
  {
    return arg.toRemove!=0;
  }
};

struct BackwardDemodulation::RewritableClausesFn
{
  RewritableClausesFn(DemodulationSubtermIndex* index) : _index(index) {}
  DECL_RETURN_TYPE(VirtualIterator<pair<TermList,TermQueryResult> >);
  OWN_RETURN_TYPE operator() (TermList lhs)
  {
    return pvi( pushPairIntoRightIterator(lhs, _index->getInstances(lhs, true)) );
  }
private:
  DemodulationSubtermIndex* _index;
};


struct BackwardDemodulation::ResultFn
{
  typedef DHMultiset<Clause*> ClauseSet;

  ResultFn(Clause* cl) : _cl(cl)
  {
    ASS_EQ(_cl->length(),1);
    _eqLit=(*_cl)[0];
    _removed=SmartPtr<ClauseSet>(new ClauseSet());
  }
  DECL_RETURN_TYPE(BwSimplificationRecord);
  /**
   * Return pair of clauses. First clause is being replaced,
   * and the second is the clause, that replaces it. If no
   * replacement should occur, return pair of zeroes.
   */
  OWN_RETURN_TYPE operator() (pair<TermList,TermQueryResult> arg)
  {
    TermQueryResult qr=arg.second;

    if( (_cl->color()|qr.clause->color())==COLOR_INVALID ) {
      //colors of premises don't match
      ASS_REP(false, "We think this should not happen. If it does and there isn't any bug, remove this assertion.");
      return BwSimplificationRecord(0);
    }

    if(_cl==qr.clause || _removed->find(qr.clause)) {
      //the retreived clause was already replaced during this
      //backward demodulation
      return BwSimplificationRecord(0);
    }

    TermList lhs=arg.first;
    TermList rhs=EqHelper::getRHS(_eqLit, lhs);

    TermList lhsS=qr.term;
    TermList rhsS;

//    if(!qr.substitution->isIdentityOnResult()) {
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
//    } else {
//      rhsS=qr.substitution->applyToQuery(rhs);
//    }

    static Ordering* ordering=0;
    if(!ordering) {
      ordering=Ordering::instance();
    }
    if(ordering->compare(lhsS,rhsS)!=Ordering::GREATER) {
      return BwSimplificationRecord(0);
    }

    Literal* resLit=EqHelper::replace(qr.literal,lhsS,rhsS);
    if(EqHelper::isEqTautology(resLit)) {
      env.statistics->backwardDemodulationsToEqTaut++;
      _removed->insert(qr.clause);
      return BwSimplificationRecord(qr.clause);
    }


    Inference* inf = new Inference2(Inference::BACKWARD_DEMODULATION, _cl, qr.clause);
    Unit::InputType inpType = (Unit::InputType)
	Int::max(_cl->inputType(), qr.clause->inputType());

    unsigned cLen=qr.clause->length();
    Clause* res = new(cLen) Clause(cLen, inpType, inf);

    (*res)[0]=resLit;

    unsigned next=1;
    for(unsigned i=0;i<cLen;i++) {
      Literal* curr=(*qr.clause)[i];
      if(curr!=qr.literal) {
	(*res)[next++] = curr;
      }
    }
    ASS_EQ(next,cLen);

    res->setAge(qr.clause->age());
    env.statistics->backwardDemodulations++;

    _removed->insert(qr.clause);
    return BwSimplificationRecord(qr.clause,res);
  }
private:
  Literal* _eqLit;
  Clause* _cl;
  SmartPtr<ClauseSet> _removed;
};


void BackwardDemodulation::perform(Clause* cl,
	BwSimplificationRecordIterator& simplifications)
{
  CALL("BackwardDemodulation::perform");

  if(cl->length()!=1 || !(*cl)[0]->isEquality() || !(*cl)[0]->isPositive() ) {
    simplifications=BwSimplificationRecordIterator::getEmpty();
    return;
  }
  Literal* lit=(*cl)[0];

  BwSimplificationRecordIterator replacementIterator=
    pvi( getFilteredIterator(
	    getMappingIterator(
		    getMapAndFlattenIterator(
			    EqHelper::getDemodulationLHSIterator(lit),
			    RewritableClausesFn(_index)),
		    ResultFn(cl)),
 	    RemovedIsNonzeroFn()) );

  //here we know that the getPersistentIterator evaluates all items of the
  //replacementIterator right at this point, so we can measure the time just
  //simply (which cannot be generally done when iterators are involved)

  TimeCounter tc(TC_BACKWARD_DEMODULATION);
  simplifications=getPersistentIterator(replacementIterator);
}

}

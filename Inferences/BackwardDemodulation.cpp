/**
 * @file BackwardDemodulation.cpp
 * Implements class SLQueryBackwardSubsumption.
 */


#include "../Lib/DHMultiset.hpp"
#include "../Lib/Environment.hpp"
#include "../Lib/Int.hpp"
#include "../Lib/List.hpp"
#include "../Lib/Metaiterators.hpp"
#include "../Lib/VirtualIterator.hpp"

#include "../Kernel/Term.hpp"
#include "../Kernel/Clause.hpp"
#include "../Kernel/MMSubstitution.hpp"
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

struct BackwardDemodulation::FirstInPairIsNonzeroFn
{
  DECL_RETURN_TYPE(bool);
  OWN_RETURN_TYPE operator() (pair<Clause*,Clause*> arg)
  {
    return arg.first!=0;
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
  DECL_RETURN_TYPE(pair<Clause*,Clause*>);
  /**
   * Return pair of clauses. First clause is being replaced,
   * and the second is the clause, that replaces it. If no
   * replacement should occur, return pair of zeroes.
   */
  OWN_RETURN_TYPE operator() (pair<TermList,TermQueryResult> arg)
  {
    TermQueryResult qr=arg.second;

    if(_removed->find(qr.clause)) {
      //the retreived clause was already replaced during this
      //backward demodulation
      return pair<Clause*,Clause*>(0,0);
    }

    TermList lhs=arg.first;
    TermList rhs=EqHelper::getRHS(_eqLit, lhs);

    TermList lhsS=qr.term;
    TermList rhsS;

    if(!qr.substitution->isIdentityOnResult()) {
      //When we apply substitution to the rhs, we get a term, that is
      //a variant of the term we'd like to get, as new variables are
      //produced in the substitution application.
      //This will be fixed once something better than MMSubstitution will
      //be used to retrieve substitutions from indexes.
      TermList lhsSBadVars=qr.substitution->applyToQuery(lhs);
      TermList rhsSBadVars=qr.substitution->applyToQuery(rhs);
      Renaming rNorm, qNorm, qDenorm;
      Renaming::normalizeVariables(lhsSBadVars, rNorm);
      Renaming::normalizeVariables(lhsS, qNorm);
      Renaming::inverse(qNorm, qDenorm);
      ASS_EQ(lhsS,qDenorm.apply(rNorm.apply(lhsSBadVars)));
      rhsS=qDenorm.apply(rNorm.apply(rhsSBadVars));
    } else {
      rhsS=qr.substitution->applyToQuery(rhs);
    }

    static Ordering* ordering=0;
    if(!ordering) {
      ordering=Ordering::instance();
    }
    if(ordering->compare(lhsS,rhsS)!=Ordering::GREATER) {
      return pair<Clause*,Clause*>(0,0);
    }

    Inference* inf = new Inference2(Inference::BACKWARD_DEMODULATION, _cl, qr.clause);
    Unit::InputType inpType = (Unit::InputType)
	Int::max(_cl->inputType(), qr.clause->inputType());

    unsigned cLen=qr.clause->length();
    Clause* res = new(cLen) Clause(cLen, inpType, inf);

    (*res)[0]=EqHelper::replace(qr.literal,lhsS,rhsS);

    unsigned next=1;
    for(unsigned i=0;i<cLen;i++) {
      Literal* curr=(*qr.clause)[i];
      if(curr!=qr.literal) {
	(*res)[next++] = curr;
      }
    }
    ASS_EQ(next,cLen);

    res->setAge(Int::max(_cl->age(),qr.clause->age())+1);
    env.statistics->backwardDemodulations++;

    _removed->insert(qr.clause);
    return make_pair(qr.clause,res);
  }
private:
  Literal* _eqLit;
  Clause* _cl;
  SmartPtr<ClauseSet> _removed;
};


void BackwardDemodulation::perform(Clause* cl,
	ClauseIterator& toRemove, ClauseIterator& toAdd)
{
  CALL("BackwardDemodulation::perform");

  if(cl->length()!=1 || !(*cl)[0]->isEquality() || !(*cl)[0]->isPositive() ) {
    toAdd=ClauseIterator::getEmpty();
    toRemove=ClauseIterator::getEmpty();
    return;
  }
  Literal* lit=(*cl)[0];

  VirtualIterator<pair<Clause*,Clause*> > replacementIterator=
    pvi( getFilteredIterator(
	    getMappingIterator(
		    getMapAndFlattenIterator(
			    EqHelper::getLHSIterator(lit),
			    RewritableClausesFn(_index)),
		    ResultFn(cl)),
	    FirstInPairIsNonzeroFn()) );

  ClauseList* toRemoveLst=0;
  ClauseList* toAddLst=0;
  while(replacementIterator.hasNext()) {
    pair<Clause*,Clause*> replacement=replacementIterator.next();
    ClauseList::push(replacement.first, toRemoveLst);
    ClauseList::push(replacement.second, toAddLst);
  }

  toAdd=getPersistentIterator(ClauseList::Iterator(toAddLst));
  toRemove=getPersistentIterator(ClauseList::Iterator(toRemoveLst));
  return;
}

}

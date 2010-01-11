/**
 * @file AWPassiveClauseContainer.cpp
 * Implements class AWPassiveClauseContainer for the queue of passive clauses.
 * @since 30/12/2007 Manchester
 */

#include "../Lib/Environment.hpp"
#include "../Lib/Int.hpp"
#include "../Lib/Timer.hpp"
#include "../Kernel/Term.hpp"
#include "../Kernel/Clause.hpp"
#include "../Shell/Statistics.hpp"
#include "../Shell/Options.hpp"

#include "SaturationAlgorithm.hpp"

#if VDEBUG
#include <iostream>
#endif

#include "AWPassiveClauseContainer.hpp"

//TODO: this should be made into Vampire option, and the different weights reflected in clause deletion in LRS
#define AXIOM_AGE_DISCRIMINATION 0

namespace Saturation
{
using namespace Lib;
using namespace Kernel;

int AWPassiveClauseContainer::s_nwcNumerator=-1;
int AWPassiveClauseContainer::s_nwcDenominator=-1;


AWPassiveClauseContainer::AWPassiveClauseContainer()
: _balance(0), _size(0)
{
  s_nwcNumerator=static_cast<int>(env.options->nongoalWeightCoefficient()*100);
  s_nwcDenominator=100;
}

Comparison AWPassiveClauseContainer::compareWeight(Clause* cl1, Clause* cl2)
{
  ASS_G(s_nwcDenominator,0);
  ASS_G(s_nwcNumerator,0);
#if AXIOM_AGE_DISCRIMINATION
  long w1, w2;
  if(cl1->inputType()==0) {
    w1=static_cast<long>(cl1->weight())*s_nwcNumerator*(cl1->age()+1);
  }
  else {
    w1=static_cast<long>(cl1->weight())*s_nwcDenominator;
  }
  if(cl2->inputType()==0) {
    w2=static_cast<long>(cl2->weight())*s_nwcNumerator*(cl2->age()+1);
  }
  else {
    w2=static_cast<long>(cl2->weight())*s_nwcDenominator;
  }
  return Int::compare(w1,w2);
#else
  if(cl1->inputType()==0 && cl2->inputType()!=0) {
    return Int::compare(cl1->weight()*s_nwcNumerator, cl2->weight()*s_nwcDenominator);
  } else if(cl1->inputType()!=0 && cl2->inputType()==0) {
    return Int::compare(cl1->weight()*s_nwcDenominator, cl2->weight()*s_nwcNumerator);
  }
  return Int::compare(cl1->weight(), cl2->weight());
#endif
}

/**
 * Comparison of clauses. The comparison uses four orders in the
 * following order:
 * <ol><li>by weight;</li>
 *     <li>by age;</li>
 *     <li>by input type;</li>
 *     <li>by number.</li>
 * </ol>
 * @since 30/12/2007 Manchester
 */
bool WeightQueue::lessThan(Clause* c1,Clause* c2)
{
  CALL("WeightQueue::lessThan");

  Comparison weightCmp=AWPassiveClauseContainer::compareWeight(c1,c2);
  if(weightCmp!=EQUAL) {
    return weightCmp==LESS;
  }

  if (c1->age() < c2->age()) {
    return true;
  }
  if (c2->age() < c1->age()) {
    return false;
  }
  if (c1->inputType() < c2->inputType()) {
    return false;
  }
  if (c2->inputType() < c1->inputType()) {
    return true;
  }
  return c1->number() < c2->number();
} // WeightQueue::lessThan


/**
 * Comparison of clauses. The comparison uses four orders in the
 * following order:
 * <ol><li>by age;</li>
 *     <li>by weight;</li>
 *     <li>by input type;</li>
 *     <li>by number.</li>
 * </ol>
 * @since 30/12/2007 Manchester
 */
bool AgeQueue::lessThan(Clause* c1,Clause* c2)
{
  CALL("AgeQueue::lessThan");

  if (c1->age() < c2->age()) {
    return true;
  }
  if (c2->age() < c1->age()) {
    return false;
  }

  Comparison weightCmp=AWPassiveClauseContainer::compareWeight(c1,c2);
  if(weightCmp!=EQUAL) {
    return weightCmp==LESS;
  }

  if (c1->inputType() < c2->inputType()) {
    return false;
  }
  if (c2->inputType() < c1->inputType()) {
    return true;
  }
  return c1->number() < c2->number();
} // WeightQueue::lessThan


AWPassiveClauseContainer::~AWPassiveClauseContainer()
{
  ClauseQueue::Iterator cit(_ageQueue);
  while(cit.hasNext()) {
    Clause* cl=cit.next();
    if(cl->store()==Clause::PASSIVE) {
      cl->setStore(Clause::NONE);
    } else if(cl->store()==Clause::REACTIVATED) {
      cl->setStore(Clause::ACTIVE);
    }
#if VDEBUG
    else {
      ASSERTION_VIOLATION;
    }
#endif
  }
}

/**
 * Add @b c clause in the queue.
 * @since 31/12/2007 Manchester
 */
void AWPassiveClauseContainer::add(Clause* cl)
{
  CALL("AWPassiveClauseContainer::add");
  ASS(_ageRatio > 0 || _weightRatio > 0);

  if (_ageRatio) {
    _ageQueue.insert(cl);
  }
  if (_weightRatio) {
    _weightQueue.insert(cl);
  }
  _size++;
  if(cl->store()!=Clause::REACTIVATED) {
    addedEvent.fire(cl);
  }
} // AWPassiveClauseContainer::add

/**
 * Return the next selected clause and remove it from the queue.
 * @since 31/12/2007 Manchester
 */
Clause* AWPassiveClauseContainer::popSelected()
{
  CALL("AWPassiveClauseContainer::popSelected");
  ASS( ! isEmpty());

  _size--;

  bool byWeight;
  if (! _ageRatio) {
    byWeight = true;
  }
  else if (! _weightRatio) {
    byWeight = false;
  }
  else if (_balance > 0) {
    byWeight = true;
  }
  else if (_balance < 0) {
    byWeight = false;
  }
  else {
    byWeight = (_ageRatio <= _weightRatio);
  }

  if (byWeight) {
    _balance -= _ageRatio;
    Clause* cl = _weightQueue.pop();
    _ageQueue.remove(cl);
    selectedEvent.fire(cl);
    return cl;
  }
  _balance += _weightRatio;
  Clause* cl = _ageQueue.pop();
  _weightQueue.remove(cl);
  selectedEvent.fire(cl);
  return cl;
} // AWPassiveClauseContainer::popSelected

void AWPassiveClauseContainer::updateLimits(long estReachableCnt)
{
  CALL("AWPassiveClauseContainer::updateLimits");
  ASS_GE(estReachableCnt,0);

  int maxAge, maxWeight;

  if(estReachableCnt>static_cast<long>(_size)) {
    maxAge=-1;
    maxWeight=-1;
    goto fin;
  }

  {
    ClauseQueue::Iterator wit(_weightQueue);
    ClauseQueue::Iterator ait(_ageQueue);

    if(!wit.hasNext() && !ait.hasNext()) {
      //passive container is empty
      return;
    }

    long remains=estReachableCnt;
    Clause* wcl=0;
    Clause* acl=0;
    if(_ageRatio==0) {
      ASS(wit.hasNext());
      while( remains && wit.hasNext() ) {
	wcl=wit.next();
	remains--;
      }
    } else if(_weightRatio==0) {
      ASS(ait.hasNext());
      while( remains && ait.hasNext() ) {
	acl=ait.next();
	remains--;
      }
    } else {
      ASS(wit.hasNext()&&ait.hasNext());

      unsigned balance=(_ageRatio<=_weightRatio)?1:0;
      while(remains) {
	ASS_G(remains,0);
	if( (balance>0 || !ait.hasNext()) && wit.hasNext()) {
	  wcl=wit.next();
	  if(!acl || wcl->age() >= acl->age()) {
	    balance-=_ageRatio;
	    remains--;
	  }
	} else if(ait.hasNext()){
	  acl=ait.next();
	  if(!wcl || acl->getEffectiveWeight() > wcl->getEffectiveWeight()) {
	    balance+=_weightRatio;
	    remains--;
	  }
	} else {
	  break;
	}
      }
    }

    //when _ageRatio==0, the age limit can be set to zero, as age doesn't matter
    maxAge=(_ageRatio && acl!=0)?-1:0;
    maxWeight=(_weightRatio && wcl!=0)?-1:0;
    if(acl!=0 && ait.hasNext()) {
      maxAge=acl->age();
    }
    if(wcl!=0 && wit.hasNext()) {
      maxWeight=static_cast<int>(wcl->getEffectiveWeight());
    }
  }

fin:
#if OUTPUT_LRS_DETAILS
  cout<<env.timer->elapsedDeciseconds()<<"\tLimits to "<<maxAge<<"\t"<<maxWeight<<"\t by est "<<estReachableCnt<<"\n";
#endif

  getSaturationAlgorithm()->getLimits()->setLimits(maxAge,maxWeight);
}

void AWPassiveClauseContainer::onLimitsUpdated(LimitsChangeType change)
{
  CALL("AWPassiveClauseContainer::onLimitsUpdated");

  if(change==LIMITS_LOOSENED) {
    return;
  }

  Limits* limits=getSaturationAlgorithm()->getLimits();
  if( (!limits->ageLimited() && _ageRatio) || (!limits->weightLimited() && _weightRatio) ) {
    return;
  }

  //Here we rely on (and maintain) the invariant, that
  //_weightQueue and _ageQueue contain the same set
  //of clauses, differing only in their order.
  //(unless one of _ageRation or _weightRatio is equal to 0)

  int ageLimit=limits->ageLimit();
  int weightLimit=limits->weightLimit();

  static Stack<Clause*> toRemove(256);
  ClauseQueue::Iterator wit(_weightQueue);
  while(wit.hasNext()) {
    Clause* cl=wit.next();
//    bool shouldStay=limits->fulfillsLimits(cl);
    bool shouldStay=true;
//    if(shouldStay && cl->age()==ageLimit) {
    if(cl->age()>ageLimit) {
      if(cl->getEffectiveWeight()>weightLimit) {
        shouldStay=false;
      }
    } else if(cl->age()==ageLimit) {
      //clauses inferred from the clause will be over age limit...
      unsigned clen=cl->length();
      int maxSelWeight=0;
      for(unsigned i=0;i<clen;i++) {
        maxSelWeight=max((int)(*cl)[i]->weight(),maxSelWeight);
      }
      //here we don't use the effective weight, as from a nongoal clause
      //can be the goal one inferred.
      if(cl->weight()-maxSelWeight>=weightLimit) {
	//and also over weight limit
        shouldStay=false;
      }
    }
    if(!shouldStay) {
      toRemove.push(cl);
    }
  }

#if OUTPUT_LRS_DETAILS
  if(toRemove.isNonEmpty()) {
    cout<<toRemove.size()<<" passive deleted, "<< (size()-toRemove.size()) <<" remains\n";
  }
#endif

  while(toRemove.isNonEmpty()) {
    Clause* removed=toRemove.pop();

    if(removed->store()!=Clause::REACTIVATED) {
      env.statistics->discardedNonRedundantClauses++;
    }

    remove(removed);
  }

}

}

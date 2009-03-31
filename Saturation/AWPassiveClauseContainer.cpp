/**
 * @file Passive.cpp
 * Implements class Passive for the queue of passive clauses.
 * @since 30/12/2007 Manchester
 */

#include "../Lib/Environment.hpp"
#include "../Lib/Timer.hpp"
#include "../Kernel/Term.hpp"
#include "../Kernel/Clause.hpp"
#include "../Shell/Statistics.hpp"

#include "SaturationAlgorithm.hpp"

#if VDEBUG
#include <iostream>
#endif

#include "AWPassiveClauseContainer.hpp"

using namespace Kernel;
using namespace Saturation;

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

  if (c1->weight() < c2->weight()) {
    return true;
  }
  if (c2->weight() < c1->weight()) {
    return false;
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
  if (c1->weight() < c2->weight()) {
    return true;
  }
  if (c2->weight() < c1->weight()) {
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


AWPassiveClauseContainer::~AWPassiveClauseContainer()
{
  ClauseQueue::Iterator cit(_ageQueue);
  while(cit.hasNext()) {
    Clause* cl=cit.next();
    cl->setStore(Clause::NONE);
  }
}

/**
 * Add @b c clause in the queue.
 * @since 31/12/2007 Manchester
 */
void AWPassiveClauseContainer::add(Clause* c)
{
  CALL("AWPassiveClauseContainer::add");
  ASS(_ageRatio > 0 || _weightRatio > 0);

  if (_ageRatio) {
    _ageQueue.insert(c);
  }
  if (_weightRatio) {
    _weightQueue.insert(c);
  }
  _size++;
  c->setStore(Clause::PASSIVE);
  env.statistics->passiveClauses++;
  addedEvent.fire(c);
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
    Clause* c = _weightQueue.pop();
    _ageQueue.remove(c);
    return c;
  }
  _balance += _weightRatio;
  Clause* c = _ageQueue.pop();
  _weightQueue.remove(c);
  selectedEvent.fire(c);
  return c;
} // AWPassiveClauseContainer::popSelected

void AWPassiveClauseContainer::updateLimits(long estReachableCnt)
{
  CALL("AWPassiveClauseContainer::updateLimits");
  ASS_GE(estReachableCnt,0);

  ClauseQueue::Iterator wit(_weightQueue);
  ClauseQueue::Iterator ait(_ageQueue);

  if(!wit.hasNext() && !ait.hasNext()) {
    return;
  }

  ASS(wit.hasNext()&&ait.hasNext());
  long remains=estReachableCnt;
  Clause* wcl=0;
  Clause* acl=0;
  unsigned balance=(_ageRatio<=_weightRatio)?1:0;
  while(remains) {
    ASS_G(remains,0);
    if( (balance>0 || !ait.hasNext()) && wit.hasNext()) {
      wcl=wit.next();
      balance-=_ageRatio;
      if(!acl || wcl->age() >= acl->age()) {
	remains--;
      }
    } else if(ait.hasNext()){
      acl=ait.next();
      balance+=_weightRatio;
      if(!wcl || acl->weight() > wcl->weight()) {
	remains--;
      }
    } else {
      break;
    }
  }

  //when _ageRatio==0, the age limit can be set to zero, as age doesn't matter
  int maxAge=(_ageRatio && acl!=0)?-1:0;
  int maxWeight=(_weightRatio && wcl!=0)?-1:0;
  if(acl!=0 && ait.hasNext()) {
    maxAge=acl->age();
  }
  if(wcl!=0 && wit.hasNext()) {
    maxWeight=wcl->weight();
  }

//  cout<<env.timer->elapsedDeciseconds()<<"\tLimits to "<<maxAge<<"\t"<<maxWeight<<"\t by est "<<estReachableCnt<<"\n";

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
  //(unless one of _ageRation or _weightRation is equal to 0)

  int ageLimit=limits->ageLimit();
  int weightLimit=limits->weightLimit();

  static Stack<Clause*> toRemove(256);
  ClauseQueue::Iterator wit(_weightQueue);
  while(wit.hasNext()) {
    Clause* cl=wit.next();
    bool shouldStay=limits->fulfillsLimits(cl);
    if(shouldStay && cl->age()==ageLimit) {
      //clauses inferred from the clause will be over age limit
      unsigned clen=cl->length();
      unsigned maxSelWeight=0;
      for(unsigned i=0;i<clen;i++) {
        maxSelWeight=max((*cl)[i]->weight(),maxSelWeight);
      }
      if(cl->weight()-maxSelWeight>=weightLimit) {
        shouldStay=false;
      }
    }
    if(!shouldStay) {
      toRemove.push(cl);
    }
  }

//  if(toRemove.isNonEmpty()) {
//    cout<<toRemove.size()<<" passive deleted\n";
//  }

  while(toRemove.isNonEmpty()) {
    remove(toRemove.pop());
  }

}




/*
 * File AWPassiveClauseContainer.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file AWPassiveClauseContainer.cpp
 * Implements class AWPassiveClauseContainer for the queue of passive clauses.
 * @since 30/12/2007 Manchester
 */

#include <math.h>

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/Timer.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/TermIterators.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/Options.hpp"

#include "SaturationAlgorithm.hpp"

#if VDEBUG
#include <iostream>
#endif

#include "AWPassiveClauseContainer.hpp"

namespace Saturation
{
using namespace Lib;
using namespace Kernel;


AWPassiveClauseContainer::AWPassiveClauseContainer(const Options& opt)
:  _ageQueue(opt), _weightQueue(opt), _balance(0), _size(0), _opt(opt)
{
  CALL("AWPassiveClauseContainer::AWPassiveClauseContainer");

  _ageRatio = _opt.ageRatio();
  _weightRatio = _opt.weightRatio();
  ASS_GE(_ageRatio, 0);
  ASS_GE(_weightRatio, 0);
  ASS(_ageRatio > 0 || _weightRatio > 0);
}

AWPassiveClauseContainer::~AWPassiveClauseContainer()
{
  ClauseQueue::Iterator cit(_ageQueue);
  while (cit.hasNext()) {
    Clause* cl=cit.next();
    ASS(cl->store()==Clause::PASSIVE);
    cl->setStore(Clause::NONE);
  }
}

ClauseIterator AWPassiveClauseContainer::iterator()
{
  return pvi( ClauseQueue::Iterator(_weightQueue) );
}

/**
 * Weight comparison of clauses.
 * @return the result of comparison (LESS, EQUAL or GREATER)
 * @warning if the option increased_numeral_weight is on, then each comparison
 *          recomputes the numeral weight of clauses, see Clause::getNumeralWeight(), so it
 *          it can be expensive
 */
Comparison AWPassiveClauseContainer::compareWeight(Clause* cl1, Clause* cl2, const Options& opt)
{
  CALL("AWPassiveClauseContainer::compareWeight");

  // TODO consider using Clause::getEffectiveWeight
  // since 22/1/15 weight now includes splitWeight
  unsigned cl1Weight=cl1->weight();
  unsigned cl2Weight=cl2->weight();

  if (opt.increasedNumeralWeight()) {
    cl1Weight=cl1Weight*2+cl1->getNumeralWeight();
    cl2Weight=cl2Weight*2+cl2->getNumeralWeight();
  }

  static int nwcNumer = opt.nonGoalWeightCoeffitientNumerator();
  static int nwcDenom = opt.nonGoalWeightCoeffitientDenominator();
  static bool restrictNWC = opt.restrictNWCtoGC();

  bool cl1_goal = cl1->isGoal();
  bool cl2_goal = cl2->isGoal();

  if(cl1_goal && restrictNWC){
    bool found = false;
    for(unsigned i=0;i<cl1->length();i++){
      TermFunIterator it((*cl1)[i]);
      it.next(); // skip literal symbol
      while(it.hasNext()){
        found |= env.signature->getFunction(it.next())->inGoal();
      }
    }
    if(!found){ cl1_goal=false; }
  }
  if(cl2_goal && restrictNWC){
    bool found = false;
    for(unsigned i=0;i<cl2->length();i++){
      TermFunIterator it((*cl2)[i]);
      it.next(); // skip literal symbol
      while(it.hasNext()){
        found |= env.signature->getFunction(it.next())->inGoal();
      }
    }
    if(!found){ cl2_goal=false; }
  }
  

  if (!cl1->isGoal() && cl2->isGoal()) {
    return Int::compare(cl1Weight*nwcNumer, cl2Weight*nwcDenom);
  } else if (cl1->isGoal() && !cl2->isGoal()) {
    return Int::compare(cl1Weight*nwcDenom, cl2Weight*nwcNumer);
  }
  return Int::compare(cl1Weight, cl2Weight);
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

  Comparison weightCmp=AWPassiveClauseContainer::compareWeight(c1, c2, _opt);
  if (weightCmp!=EQUAL) {
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

  Comparison weightCmp=AWPassiveClauseContainer::compareWeight(c1, c2, _opt);
  if (weightCmp!=EQUAL) {
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
  addedEvent.fire(cl);
} // AWPassiveClauseContainer::add

/**
 * Remove Clause from the Passive store. Should be called only
 * when the Clause is no longer needed by the inference process
 * (i.e. was backward subsumed/simplified), as it can result in
 * deletion of the clause.
 */
void AWPassiveClauseContainer::remove(Clause* cl)
{
  CALL("AWPassiveClauseContainer::remove");
  ASS(cl->store()==Clause::PASSIVE);

  if (_ageRatio) {
    ALWAYS(_ageQueue.remove(cl));
  }
  if (_weightRatio) {
    ALWAYS(_weightQueue.remove(cl));
  }
  _size--;

  removedEvent.fire(cl);

  ASS(cl->store()!=Clause::PASSIVE);
}


/**
 * Return the next selected clause and remove it from the queue.
 * @since 31/12/2007 Manchester
 */
Clause* AWPassiveClauseContainer::popSelected()
{
  CALL("AWPassiveClauseContainer::popSelected");
  ASS( ! isEmpty());

	static unsigned count = 0;
	count++;

	auto shape = _opt.ageWeightRatioShape();
	unsigned frequency = _opt.ageWeightRatioShapeFrequency();
	if(shape != Options::AgeWeightRatioShape::CONSTANT) {

		if(shape == Options::AgeWeightRatioShape::DECAY && count % frequency == 0) {
			// decide if we need to modify age or weight
			int *toModify = _ageRatio < _weightRatio ? &_weightRatio : &_ageRatio;

			// decay it a bit...
			int next = *toModify / 2;
			// but make sure it's non-zero if it was to start with
			if(next == 0 && *toModify != 0) {
				next = 1;
			}
			*toModify = next;
		}
	}

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



void AWPassiveClauseContainer::updateLimits(long long estReachableCnt)
{
  CALL("AWPassiveClauseContainer::updateLimits");
  ASS_GE(estReachableCnt,0);

  int maxAge, maxWeight;

  if (estReachableCnt>static_cast<long long>(_size)) {
    maxAge=-1;
    maxWeight=-1;
    goto fin;
  }

  {
    ClauseQueue::Iterator wit(_weightQueue);
    ClauseQueue::Iterator ait(_ageQueue);

    if (!wit.hasNext() && !ait.hasNext()) {
      //passive container is empty
      return;
    }

    long long remains=estReachableCnt;
    Clause* wcl=0;
    Clause* acl=0;
    if (_ageRatio==0 || (_opt.lrsWeightLimitOnly() && _weightRatio!=0) ) {
      ASS(wit.hasNext());
      while ( remains && wit.hasNext() ) {
	wcl=wit.next();
	remains--;
      }
    } else if (_weightRatio==0) {
      ASS(ait.hasNext());
      while ( remains && ait.hasNext() ) {
	acl=ait.next();
	remains--;
      }
    } else {
      ASS(wit.hasNext()&&ait.hasNext());

      int balance=(_ageRatio<=_weightRatio)?1:0;
      while (remains) {
	ASS_G(remains,0);
	if ( (balance>0 || !ait.hasNext()) && wit.hasNext()) {
	  wcl=wit.next();
	  if (!acl || _ageQueue.lessThan(acl, wcl)) {
	    balance-=_ageRatio;
	    remains--;
	  }
	} else if (ait.hasNext()){
	  acl=ait.next();
	  if (!wcl || _weightQueue.lessThan(wcl, acl)) {
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
    if (acl!=0 && ait.hasNext()) {
      maxAge=acl->age();
    }
    if (wcl!=0 && wit.hasNext()) {
      maxWeight=static_cast<int>(ceil(wcl->getEffectiveWeight(_opt)));
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

  if (change==LIMITS_LOOSENED) {
    return;
  }

  Limits* limits=getSaturationAlgorithm()->getLimits();
  if ( (!limits->ageLimited() && _ageRatio) || (!limits->weightLimited() && _weightRatio) ) {
    return;
  }

  //Here we rely on (and maintain) the invariant, that
  //_weightQueue and _ageQueue contain the same set
  //of clauses, differing only in their order.
  //(unless one of _ageRation or _weightRatio is equal to 0)

  unsigned ageLimit=limits->ageLimit();
  unsigned weightLimit=limits->weightLimit();

  static Stack<Clause*> toRemove(256);
  ClauseQueue::Iterator wit(_weightQueue);
  while (wit.hasNext()) {
    Clause* cl=wit.next();
//    bool shouldStay=limits->fulfillsLimits(cl);
    bool shouldStay=true;
//    if (shouldStay && cl->age()==ageLimit) {
    if (cl->age()>ageLimit) {
      if (cl->getEffectiveWeight(_opt)>weightLimit) {
        shouldStay=false;
      }
    } else if (cl->age()==ageLimit) {
      //clauses inferred from the clause will be over age limit...
      unsigned clen=cl->length();
      int maxSelWeight=0;
      for(unsigned i=0;i<clen;i++) {
        maxSelWeight=max((int)(*cl)[i]->weight(),maxSelWeight);
      }
      //here we don't use the effective weight, as from a nongoal clause
      //can be the goal one inferred.
      // splitWeight is now used in weight() though
      if (cl->weight()-maxSelWeight>=weightLimit) {
	//and also over weight limit
        shouldStay=false;
      }
    }
    if (!shouldStay) {
      toRemove.push(cl);
    }
  }

#if OUTPUT_LRS_DETAILS
  if (toRemove.isNonEmpty()) {
    cout<<toRemove.size()<<" passive deleted, "<< (size()-toRemove.size()) <<" remains\n";
  }
#endif

  while (toRemove.isNonEmpty()) {
    Clause* removed=toRemove.pop();
    RSTAT_CTR_INC("clauses discarded from passive on weight limit update");
    env.statistics->discardedNonRedundantClauses++;
    remove(removed);
  }
}

AWClauseContainer::AWClauseContainer(const Options& opt)
: _ageQueue(opt), _weightQueue(opt), _ageRatio(1), _weightRatio(1), _balance(0), _size(0)
{
}

bool AWClauseContainer::isEmpty() const
{
  CALL("AWClauseContainer::isEmpty");

  ASS(!_ageRatio || !_weightRatio || _ageQueue.isEmpty()==_weightQueue.isEmpty());
  return _ageQueue.isEmpty() && _weightQueue.isEmpty();
}

/**
 * Add @b c clause in the queue.
 * @since 31/12/2007 Manchester
 */
void AWClauseContainer::add(Clause* cl)
{
  CALL("AWClauseContainer::add");
  ASS(_ageRatio > 0 || _weightRatio > 0);

  if (_ageRatio) {
    _ageQueue.insert(cl);
  }
  if (_weightRatio) {
    _weightQueue.insert(cl);
  }
  _size++;
  addedEvent.fire(cl);
}

/**
 * Remove Clause from the container.
 */
bool AWClauseContainer::remove(Clause* cl)
{
  CALL("AWClauseContainer::remove");

  bool removed;
  if (_ageRatio) {
    removed = _ageQueue.remove(cl);
    if (_weightRatio) {
      ALWAYS(_weightQueue.remove(cl)==removed);
    }
  }
  else {
    ASS(_weightRatio);
    removed = _weightQueue.remove(cl);
  }

  if (removed) {
    _size--;
    removedEvent.fire(cl);
  }
  return removed;
}


/**
 * Return the next selected clause and remove it from the queue.
 */
Clause* AWClauseContainer::popSelected()
{
  CALL("AWClauseContainer::popSelected");
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

  Clause* cl;
  if (byWeight) {
    _balance -= _ageRatio;
    cl = _weightQueue.pop();
    ALWAYS(_ageQueue.remove(cl));
  }
  else {
    _balance += _weightRatio;
    cl = _ageQueue.pop();
    ALWAYS(_weightQueue.remove(cl));
  }
  selectedEvent.fire(cl);
  return cl;
}



}

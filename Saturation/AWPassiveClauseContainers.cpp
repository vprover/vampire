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
 * @file AWPassiveClauseContainers.cpp
 * Implements class AWPassiveClauseContainer for the queue of passive clauses.
 * @since 30/12/2007 Manchester
 */

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/Random.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Clause.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/Options.hpp"

#if OUTPUT_LRS_DETAILS
#include <iostream>
#endif

#include "AWPassiveClauseContainers.hpp"

namespace Saturation
{
using namespace std;
using namespace Lib;
using namespace Kernel;

/**
 * Weight comparison of clauses.
 * @return the result of comparison (LESS, EQUAL or GREATER)
 * @warning if the option increased_numeral_weight is on, then each comparison
 *          recomputes the numeral weight of clauses, see Clause::getNumeralWeight(), so it
 *          it can be expensive
 */
static Comparison compareWeight(Clause* cl1, Clause* cl2, const Options& opt)
{
  return Int::compare(cl1->weightForClauseSelection(opt), cl2->weightForClauseSelection(opt));
}

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
  if (c1->age() < c2->age()) {
    return true;
  }
  if (c2->age() < c1->age()) {
    return false;
  }

  Comparison weightCmp=compareWeight(c1, c2, _opt);
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
} // AgeQueue::lessThan

AgeQueue::OrdVal AgeQueue::getOrdVal(Clause* cl) const
{
  return std::make_pair(cl->age(),cl->weightForClauseSelection(_opt));
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
  Comparison weightCmp=compareWeight(c1, c2, _opt);
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

WeightQueue::OrdVal WeightQueue::getOrdVal(Clause* cl) const
{
  return std::make_pair(cl->weightForClauseSelection(_opt),cl->age());
}


AWPassiveClauseContainer::AWPassiveClauseContainer(bool isOutermost, const Shell::Options& opt, std::string name) :
  PassiveClauseContainer(isOutermost, opt, name),
  _ageQueue(opt),
  _weightQueue(opt),
  _ageRatio(opt.ageRatio()),
  _weightRatio(opt.weightRatio()),
  _balance(0),
  _size(0),

  _simulationBalance(0),
  _simulationCurrAgeIt(_ageQueue),
  _simulationCurrWeightIt(_weightQueue),
  _simulationCurrAgeCl(nullptr),
  _simulationCurrWeightCl(nullptr),
  _ageSelectionMaxAge(UINT_MAX),
  _ageSelectionMaxWeight(UINT_MAX),
  _weightSelectionMaxWeight(UINT_MAX)
{
  ASS_G(_ageRatio, 0);
  ASS_G(_weightRatio, 0);
}

AWPassiveClauseContainer::~AWPassiveClauseContainer()
{
  ClauseQueue::Iterator cit(_ageQueue);
  while (cit.hasNext())
  {
    Clause* cl=cit.next();
    ASS(!_isOutermost || cl->store()==Clause::PASSIVE);
    cl->setStore(Clause::NONE);
  }
}

/**
 * Add @b c clause in the queue.
 * @since 31/12/2007 Manchester
 */
void AWPassiveClauseContainer::add(Clause* cl)
{
  ASS(cl->store() == Clause::PASSIVE);

  _ageQueue.insert(cl);
  _weightQueue.insert(cl);
  _size++;

  if (_isOutermost) {
    addedEvent.fire(cl);
  }
} // AWPassiveClauseContainer::add

/**
 * Remove Clause from the Passive store. Should be called only
 * when the Clause is no longer needed by the inference process
 * (i.e. was backward subsumed/simplified), as it can result in
 * deletion of the clause.
 */
void AWPassiveClauseContainer::remove(Clause* cl)
{
  if (_isOutermost) {
    ASS(cl->store()==Clause::PASSIVE);
  }
  _ageQueue.remove(cl);
  if (_weightQueue.remove(cl)) { // _ageQueue could be used for the question too
    _size--;
  }

  if (_isOutermost) {
    removedEvent.fire(cl);
    ASS(cl->store()!=Clause::PASSIVE);
  }
}

bool AWPassiveClauseContainer::byWeight(int balance)
{
  if (balance > 0) {
    return true;
  } else if (balance < 0) {
    return false;
  } else {
    return (_ageRatio <= _weightRatio);
  }
}

/**
 * Return the next selected clause and remove it from the queue.
 * @since 31/12/2007 Manchester
 */
Clause* AWPassiveClauseContainer::popSelected()
{
  ASS(!isEmpty());

  _size--;

  Clause* cl;
  bool selByWeight = _opt.randomAWR() ?
    // we respect the ratio, but choose probabilistically
    (Random::getInteger(_ageRatio+_weightRatio) < _weightRatio) :
    // the deterministic way
    byWeight(_balance);

  if (selByWeight) {
    _balance -= _ageRatio;
    cl = _weightQueue.pop();
    _ageQueue.remove(cl);
  } else {
    _balance += _weightRatio;
    cl = _ageQueue.pop();
    _weightQueue.remove(cl);
  }

  if (_isOutermost) {
    selectedEvent.fire(cl);
  }

  return cl;
} // AWPassiveClauseContainer::popSelected

void AWPassiveClauseContainer::onLimitsUpdated()
{
  if (!ageLimited() || !weightLimited()) {
    return;
  }

  //Here we rely on (and maintain) the invariant, that
  //_weightQueue and _ageQueue contain the same set
  //of clauses, differing only in their order.
  //(unless one of _ageRation or _weightRatio is equal to 0)

  static Stack<Clause*> toRemove(256);
  ClauseQueue::Iterator wit(_weightQueue);
  while (wit.hasNext()) {
    Clause* cl=wit.next();
    if (exceedsAllLimits(cl)) {
      toRemove.push(cl);
    } else if (allChildrenNecessarilyExceedLimits(cl, cl->length())) {
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
    RSTAT_CTR_INC("clauses discarded from passive on age/weight limit update");
    env.statistics->discardedNonRedundantClauses++;
    remove(removed);
  }
}

void AWPassiveClauseContainer::simulationInit()
{
  _simulationBalance = _balance;

  // initialize iterators
  _simulationCurrAgeIt = ClauseQueue::Iterator(_ageQueue);
  _simulationCurrAgeCl = _simulationCurrAgeIt.hasNext() ? _simulationCurrAgeIt.next() : nullptr;

  _simulationCurrWeightIt = ClauseQueue::Iterator(_weightQueue);
  _simulationCurrWeightCl = _simulationCurrWeightIt.hasNext() ? _simulationCurrWeightIt.next() : nullptr;

  // have to consider two possibilities for simulation:
  // standard case: both container are initially non-empty, then have invariants
  // - _simulationCurrAgeCl != nullptr
  // - _simulationCurrWeightCl != nullptr
  // degenerate case: both containers are initially empty (e.g. happens sometimes if layered clause selection is used), then have invariant
  // - _simulationCurrAgeCl == nullptr
  // - _simulationCurrWeightCl == nullptr
  ASS(_simulationCurrAgeCl != nullptr || _simulationCurrWeightCl == nullptr);
  ASS(_simulationCurrAgeCl == nullptr || _simulationCurrWeightCl != nullptr);
}

bool AWPassiveClauseContainer::simulationHasNext()
{
  ASS(_simulationCurrAgeCl != nullptr || _simulationCurrWeightCl == nullptr);
  ASS(_simulationCurrAgeCl == nullptr || _simulationCurrWeightCl != nullptr);

  if (_simulationCurrAgeCl == nullptr)
  {
    // degenerate case: both containers are empty, so return false
    return false;
  }

  // advance _simulationCurrAgeIt, until _simulationCurrAgeCl points to a
  // clause which has not been deleted in the simulation or _simulationCurrAgeIt
  // reaches the end of the age-queue
  // establishes invariant: if there is a clause which is not deleted in the simulation, then _simulationCurrAgeCl is not deleted.
  while (_simulationCurrAgeCl->hasAux() && _simulationCurrAgeIt.hasNext())
  {
    _simulationCurrAgeCl = _simulationCurrAgeIt.next();
  }
  ASS(_simulationCurrAgeCl != nullptr);

  // advance _simulationCurrWeightIt, until _simulationCurrWeightCl points to a
  // clause which has not been deleted in the simulation or _simulationCurrWeightIt
  // reaches the end of the weight-queue
  // establishes invariant: if there is a clause which is not deleted in the simulation, then _simulationCurrWeightCl is not deleted.
  while (_simulationCurrWeightCl->hasAux() && _simulationCurrWeightIt.hasNext())
  {
    _simulationCurrWeightCl = _simulationCurrWeightIt.next();
  }
  ASS(_simulationCurrWeightCl != nullptr);

  ASS(!_simulationCurrAgeCl->hasAux() || _simulationCurrWeightCl->hasAux());
  ASS(_simulationCurrAgeCl->hasAux() || !_simulationCurrWeightCl->hasAux());

  return !_simulationCurrAgeCl->hasAux();
}

// assumes that simulationHasNext() has been called before and returned true,
// so each iterator (if used) does point to a clause which is not deleted in the simulation
void AWPassiveClauseContainer::simulationPopSelected()
{
  // invariants:
  // - both queues share the aux-field which denotes whether a clause was deleted during the simulation
  // - both queues contain the same clauses
  if (byWeight(_simulationBalance)) {
    // simulate selection by weight
    _simulationBalance -= _ageRatio;
    ASS(!_simulationCurrWeightCl->hasAux());
    _simulationCurrWeightCl->setAux();
  } else {
    // simulate selection by age
    _simulationBalance += _weightRatio;
    ASS(!_simulationCurrAgeCl->hasAux());
    _simulationCurrAgeCl->setAux();
  }
}

bool AWPassiveClauseContainer::setLimitsToMax()
{
  return setLimits(UINT_MAX, UINT_MAX, UINT_MAX);
}

bool AWPassiveClauseContainer::setLimitsFromSimulation()
{
  ASS(_simulationCurrAgeCl != nullptr || _simulationCurrWeightCl == nullptr);
  ASS(_simulationCurrAgeCl == nullptr || _simulationCurrWeightCl != nullptr);

  if (_simulationCurrAgeCl == nullptr)
  {
    // degenerate case: both containers are empty, so set limits to max.
    return setLimitsToMax();
  }
  else
  {
    ASS(!_simulationCurrAgeCl->hasAux() || _simulationCurrWeightCl->hasAux());
    ASS(_simulationCurrAgeCl->hasAux() || !_simulationCurrWeightCl->hasAux());
  }

  unsigned maxAgeQueueAge;
  unsigned maxAgeQueueWeight;
  unsigned maxWeightQueueWeight;

  // compute limits for age-queue
  if (_simulationCurrAgeIt.hasNext())
  {
    // the age-queue is in use and the simulation didn't get to the end of the age-queue => set limits on age-queue
    maxAgeQueueAge = _simulationCurrAgeCl->age();
    maxAgeQueueWeight = _simulationCurrAgeCl->weightForClauseSelection(_opt);
  }
  else
  {
    // the age-queue is in use and the simulation got to the end of the age-queue => set no limits on age-queue
    maxAgeQueueAge = UINT_MAX;
    maxAgeQueueWeight = UINT_MAX;
  }

  // compute limits for weight-queue
  if (_simulationCurrWeightIt.hasNext())
  {
    // the weight-queue is in use and the simulation didn't get to the end of the weight-queue => set limits on weight-queue
    maxWeightQueueWeight = _simulationCurrWeightCl->weightForClauseSelection(_opt);
  }
  else
  {
    // the weight-queue is in use and the simulation got to the end of the weight-queue => set no limits on weight-queue
    maxWeightQueueWeight = UINT_MAX;
  }

  // TODO: force in Options that weightRatio is positive if lrsWeightLimitOnly() is set to 'on'.
  if (_opt.lrsWeightLimitOnly())
  {
    // if the option lrsWeightLimitOnly() is set, we want to discard all clauses which are too heavy, regardless of the age.
    // we therefore make sure that fulfilsAgeLimit() always fails.
    maxAgeQueueAge = 0;
    maxAgeQueueWeight = 0;
  }

  return setLimits(maxAgeQueueAge, maxAgeQueueWeight,maxWeightQueueWeight);
}

bool AWPassiveClauseContainer::allChildrenNecessarilyExceedLimits(Clause* cl, unsigned upperBoundNumSelLits) const
{
  if (cl->age() >= _ageSelectionMaxAge)
  {
    // creating a fake inference to represent our current (pessimistic) estimate potential
    // FromInput - so that there is no Unit ownership issue
    Inference inf = FromInput(UnitInputType::CONJECTURE); // CONJECTURE, so that derivedFromGoal is estimated as true
    inf.setAge(cl->age() + 1); // clauses inferred from the clause as generating inferences will be over age limit...

    int maxSelWeight=0;
    for(unsigned i=0;i<upperBoundNumSelLits;i++) {
      maxSelWeight=max((int)(*cl)[i]->weight(),maxSelWeight);
    }
    // TODO: this lower bound is not correct:
    //       if Avatar is used, then the child-clause could become splittable,
    //       in which case we don't know any lower bound on the resulting components.
    unsigned weightLowerBound = cl->weight() - maxSelWeight; // heuristic: we assume that at most one literal will be removed from the clause.
    unsigned numPositiveLiteralsParent = cl->numPositiveLiterals();
    unsigned numPositiveLiteralsLowerBound = numPositiveLiteralsParent > 0 ? numPositiveLiteralsParent-1 : numPositiveLiteralsParent; // heuristic: we assume that at most one literal will be removed from the clause
    if (exceedsWeightLimit(weightLowerBound, numPositiveLiteralsLowerBound, inf)) {
      //and also over weight limit
      return true;
    }
  }
  return false;
}

bool AWPassiveClauseContainer::setLimits(unsigned newAgeSelectionMaxAge, unsigned newAgeSelectionMaxWeight, unsigned newWeightSelectionMaxWeight)
{
  bool atLeastOneTightened = false;
  if(newAgeSelectionMaxAge != _ageSelectionMaxAge || newAgeSelectionMaxWeight != _ageSelectionMaxWeight) {
    if(newAgeSelectionMaxAge < _ageSelectionMaxAge) {
      atLeastOneTightened = true;
    } else if (newAgeSelectionMaxAge == _ageSelectionMaxAge && newAgeSelectionMaxWeight < _ageSelectionMaxWeight) {
      atLeastOneTightened = true;
    }
    _ageSelectionMaxAge=newAgeSelectionMaxAge;
    _ageSelectionMaxWeight=newAgeSelectionMaxWeight;
  }
  if(newWeightSelectionMaxWeight != _weightSelectionMaxWeight) {
    if(newWeightSelectionMaxWeight < _weightSelectionMaxWeight) {
      atLeastOneTightened = true;
    }
    _weightSelectionMaxWeight=newWeightSelectionMaxWeight;
  }
  return atLeastOneTightened;
}

bool AWPassiveClauseContainer::ageLimited() const
{
  return _ageSelectionMaxAge != UINT_MAX && _ageSelectionMaxWeight != UINT_MAX;
}

bool AWPassiveClauseContainer::weightLimited() const
{
  return _weightSelectionMaxWeight != UINT_MAX;
}

bool AWPassiveClauseContainer::exceedsAgeLimit(unsigned, const Inference& inference, bool&) const
{
  const unsigned age = inference.age();
  return age > _ageSelectionMaxAge;
  // can't do more refined check, as we always estimate weight only by 0 the moment this function is called
}

bool AWPassiveClauseContainer::exceedsWeightLimit(unsigned w, unsigned numPositiveLiterals, const Inference& inference) const
{
  if (_weightSelectionMaxWeight == UINT_MAX) return false;

  const unsigned numeralWeight = 0; // heuristic: we don't want to compute the numeral weight during estimates and conservatively assume that it is 0.
  const unsigned splitWeight = 0; // also conservatively assuming 0
  /* In principle, we could compute this from the Inference (and it's not so expensive)
   * but it's only relevant with avatar on (and avatar would later compute the splitset of the new clause again)
   * and nonliteralsInClauseWeight on, which is not the default. So keeping the cheap version for now.
   */
  const bool derivedFromGoal = inference.derivedFromGoal();
  // If the caller was too lazy to supply an Inference object we conservatively assume that the result is a goal-clause.
  unsigned weightForClauseSelection = Clause::computeWeightForClauseSelection(w, splitWeight, numeralWeight, derivedFromGoal, _opt);
  return weightForClauseSelection > _weightSelectionMaxWeight;
}

bool AWPassiveClauseContainer::exceedsAllLimits(Clause* cl) const
{
  // here we don't need to compute weightForClauseSelection (it's been established and stored)
  unsigned age = cl->age();
  if (age < _ageSelectionMaxAge) return false;
  unsigned weightForClauseSelection = cl->weightForClauseSelection(_opt);
  if (weightForClauseSelection <= _weightSelectionMaxWeight) return false;
  if (age > _ageSelectionMaxAge) return true;
  ASS_EQ(age,_ageSelectionMaxAge);
  return weightForClauseSelection > _ageSelectionMaxWeight;
}

}

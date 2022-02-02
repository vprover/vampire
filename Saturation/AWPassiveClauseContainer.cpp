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
 * @file AWPassiveClauseContainer.cpp
 * Implements class AWPassiveClauseContainer for the queue of passive clauses.
 * @since 30/12/2007 Manchester
 */

#include <cmath>
#include <climits>

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

AWPassiveClauseContainer::AWPassiveClauseContainer(bool isOutermost, const Shell::Options& opt, vstring name) :
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
  _weightSelectionMaxWeight(UINT_MAX),
  _weightSelectionMaxAge(UINT_MAX)
{
  CALL("AWPassiveClauseContainer::AWPassiveClauseContainer");

  if(_opt.ageWeightRatioShape() == Options::AgeWeightRatioShape::CONVERGE) {
    _ageRatio = 1;
    _weightRatio = 1;
  }
  ASS_GE(_ageRatio, 0);
  ASS_GE(_weightRatio, 0);
  ASS(_ageRatio > 0 || _weightRatio > 0);
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
 * Weight comparison of clauses.
 * @return the result of comparison (LESS, EQUAL or GREATER)
 * @warning if the option increased_numeral_weight is on, then each comparison
 *          recomputes the numeral weight of clauses, see Clause::getNumeralWeight(), so it
 *          it can be expensive
 */
Comparison AWPassiveClauseContainer::compareWeight(Clause* cl1, Clause* cl2, const Options& opt)
{
  CALL("AWPassiveClauseContainer::compareWeight");

  return Int::compare(cl1->weightForClauseSelection(opt), cl2->weightForClauseSelection(opt));
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

  if(env.options->prioritiseClausesProducedByLongReduction()){
    if(c1->inference().reductions() < c2->inference().reductions()){
      return false;
    }

    if(c2->inference().reductions() < c1->inference().reductions()){
      return true;
    }
  }

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
  ASS(cl->store() == Clause::PASSIVE);

  if (_ageRatio) {
    _ageQueue.insert(cl);
  }
  if (_weightRatio) {
    _weightQueue.insert(cl);
  }
  _size++;

  if (_isOutermost)
  {
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
  CALL("AWPassiveClauseContainer::remove");
  if (_isOutermost)
  {
    ASS(cl->store()==Clause::PASSIVE);
  }
  ASS(_ageRatio > 0 || _weightRatio > 0);
  bool wasRemoved; // will be assigned, since at least one of the following checks succeeds
  if (_ageRatio) {
    wasRemoved = _ageQueue.remove(cl);
  }
  if (_weightRatio) {
    wasRemoved = _weightQueue.remove(cl);
  }

  if (wasRemoved) {
    _size--;
  }

  if (_isOutermost)
  {
    removedEvent.fire(cl);
    ASS(cl->store()!=Clause::PASSIVE);
  }
}

bool AWPassiveClauseContainer::byWeight(int balance)
{
  CALL("AWPassiveClauseContainer::byWeight");

  if (! _ageRatio) {
    return true;
  }
  else if (! _weightRatio) {
    return false;
  }
  else if (balance > 0) {
    return true;
  }
  else if (balance < 0) {
    return false;
  }
  else {
    return (_ageRatio <= _weightRatio);
  }
}

/**
 * Return the next selected clause and remove it from the queue.
 * @since 31/12/2007 Manchester
 */
Clause* AWPassiveClauseContainer::popSelected()
{
  CALL("AWPassiveClauseContainer::popSelected");
  ASS( ! isEmpty());

  auto shape = _opt.ageWeightRatioShape();
  unsigned frequency = _opt.ageWeightRatioShapeFrequency();
  static unsigned count = 0;
  count++;

  bool is_converging = shape == Options::AgeWeightRatioShape::CONVERGE;
  int targetAgeRatio = is_converging ? _opt.ageRatio() : 1;
  int targetWeightRatio = is_converging ? _opt.weightRatio() : 1;

  if(count % frequency == 0) {
    switch(shape) {
    case Options::AgeWeightRatioShape::CONSTANT:
      break;
    case Options::AgeWeightRatioShape::DECAY:
    case Options::AgeWeightRatioShape::CONVERGE:
      int ageDifference = targetAgeRatio - _ageRatio;
      int weightDifference = targetWeightRatio - _weightRatio;
      int bonus = is_converging ? 1 : -1;
      int ageUpdate = (ageDifference + bonus) / 2;
      int weightUpdate = (weightDifference + bonus) / 2;

      _ageRatio += ageUpdate;
      _weightRatio += weightUpdate;
   }
  }
  //std::cerr << _ageRatio << "\t" << _weightRatio << std::endl;
  _size--;

  Clause* cl;
  if (byWeight(_balance)) {
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
  CALL("AWPassiveClauseContainer::onLimitsUpdated");

  if ( (_ageRatio > 0 && !ageLimited()) || (_weightRatio > 0 && !weightLimited()) )
  {
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
    if (!fulfilsAgeLimit(cl) && !fulfilsWeightLimit(cl)) {
      toRemove.push(cl);
    } else if (!childrenPotentiallyFulfilLimits(cl, cl->length())) {
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

void AWPassiveClauseContainer::simulationInit()
{
  CALL("AWPassiveClauseContainer::simulationInit");
  _simulationBalance = _balance;

  // initialize iterators
  if (_ageRatio > 0)
  {
    _simulationCurrAgeIt = ClauseQueue::Iterator(_ageQueue);
    _simulationCurrAgeCl = _simulationCurrAgeIt.hasNext() ? _simulationCurrAgeIt.next() : nullptr;
  }
  if (_weightRatio > 0)
  {
    _simulationCurrWeightIt = ClauseQueue::Iterator(_weightQueue);
    _simulationCurrWeightCl = _simulationCurrWeightIt.hasNext() ? _simulationCurrWeightIt.next() : nullptr;
  }

  if (_ageRatio > 0 && _weightRatio > 0)
  {
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
}

bool AWPassiveClauseContainer::simulationHasNext()
{
  CALL("AWPassiveClauseContainer::simulationHasNext");

  // Part 1: Return false if aw-container is empty
  if (_ageRatio == 0)
  {
    if (_simulationCurrWeightCl == nullptr)
    {
      // degenerate case: weight-container is empty (and we don't use the age-container), so return false
      return false;
    }
  }
  else if (_weightRatio == 0)
  {
    if (_simulationCurrAgeCl == nullptr)
    {
      // degenerate case: age-container is empty (and we don't use the weight-container), so return false
      return false;
    }
  }
  else
  {
    ASS(_ageRatio > 0 && _weightRatio > 0);
    ASS(_simulationCurrAgeCl != nullptr || _simulationCurrWeightCl == nullptr);
    ASS(_simulationCurrAgeCl == nullptr || _simulationCurrWeightCl != nullptr);

    if (_simulationCurrAgeCl == nullptr)
    {
      // degenerate case: both containers are empty, so return false
      return false;
    }
  }

  // if we reach this point, we know that there is at least one clause in the aw-container (but it could already been deleted in the simulation)
  // Part 2: advance each iterator to point to a clause not deleted in the simulation (if possible)
  if (_ageRatio > 0)
  {
    // advance _simulationCurrAgeIt, until _simulationCurrAgeCl points to a
    // clause which has not been deleted in the simulation or _simulationCurrAgeIt
    // reaches the end of the age-queue
    // establishes invariant: if there is a clause which is not deleted in the simulation, then _simulationCurrAgeCl is not deleted.
    while (_simulationCurrAgeCl->hasAux() && _simulationCurrAgeIt.hasNext())
    {
      _simulationCurrAgeCl = _simulationCurrAgeIt.next();
    }
    ASS(_simulationCurrAgeCl != nullptr);
  }
  if (_weightRatio > 0)
  {
    // advance _simulationCurrWeightIt, until _simulationCurrWeightCl points to a
    // clause which has not been deleted in the simulation or _simulationCurrWeightIt
    // reaches the end of the weight-queue
    // establishes invariant: if there is a clause which is not deleted in the simulation, then _simulationCurrWeightCl is not deleted.
    while (_simulationCurrWeightCl->hasAux() && _simulationCurrWeightIt.hasNext())
    {
      _simulationCurrWeightCl = _simulationCurrWeightIt.next();
    }
    ASS(_simulationCurrWeightCl != nullptr);
  }

  // Part 3: return whether clause was found which is not deleted in the simulation
  if (_ageRatio == 0)
  {
    return !_simulationCurrWeightCl->hasAux();
  }
  else if (_weightRatio == 0)
  {
    return !_simulationCurrAgeCl->hasAux();
  }
  else
  {
    ASS(_ageRatio > 0 && _weightRatio > 0);
    ASS(!_simulationCurrAgeCl->hasAux() || _simulationCurrWeightCl->hasAux());
    ASS(_simulationCurrAgeCl->hasAux() || !_simulationCurrWeightCl->hasAux());

    return !_simulationCurrAgeCl->hasAux();
  }
}

// assumes that simulationHasNext() has been called before and returned true,
// so each iterator (if used) does point to a clause which is not deleted in the simulation
void AWPassiveClauseContainer::simulationPopSelected()
{
  CALL("AWPassiveClauseContainer::simulationPopSelected");

  // invariants:
  // - both queues share the aux-field which denotes whether a clause was deleted during the simulation
  // - if _ageRatio > 0 and _weightRatio > 0, then both queues contain the same clauses
  // note: byWeight() already takes care of the cases where _ageRatio == 0 or _weightRatio == 0
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
  CALL("AWPassiveClauseContainer::setLimitsToMax");
  return setLimits(UINT_MAX, UINT_MAX, UINT_MAX, UINT_MAX);
}

bool AWPassiveClauseContainer::setLimitsFromSimulation()
{
  CALL("AWPassiveClauseContainer::setLimitsFromSimulation");

  if (_ageRatio == 0)
  {
    if (_simulationCurrWeightCl == nullptr)
    {
      // degenerate case: weight-container is empty (and we don't use the age-container), so set limits to max.
      return setLimitsToMax();
    }
  }
  else if (_weightRatio == 0)
  {
    if (_simulationCurrAgeCl == nullptr)
    {
      // degenerate case: age-container is empty (and we don't use the weight-container), so set limits to max.
      return setLimitsToMax();
    }
  }
  else
  {
    ASS(_ageRatio > 0 && _weightRatio > 0);
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
  }

  unsigned maxAgeQueueAge;
  unsigned maxAgeQueueWeight;
  unsigned maxWeightQueueWeight;
  unsigned maxWeightQueueAge;

  // compute limits for age-queue
  if (_ageRatio > 0)
  {
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
  }
  else
  {
    // the age-queue is not in use, so no clause will be selected from the age-queue => set tighest possible bound on age-queue
    maxAgeQueueAge = 0;
    maxAgeQueueWeight = 0;
  }

  // compute limits for weight-queue
  if (_weightRatio > 0)
  {
    if (_simulationCurrWeightIt.hasNext())
    {
      // the weight-queue is in use and the simulation didn't get to the end of the weight-queue => set limits on weight-queue
      maxWeightQueueWeight = _simulationCurrWeightCl->weightForClauseSelection(_opt);
      maxWeightQueueAge = _simulationCurrWeightCl->age();
    }
    else
    {
      // the weight-queue is in use and the simulation got to the end of the weight-queue => set no limits on weight-queue
      maxWeightQueueWeight = UINT_MAX;
      maxWeightQueueAge = UINT_MAX;
    }
  }
  else
  {
    // the weight-queue is not in use, so no clause will be selected from the weight-queue => set tighest possible bound on weight-queue
    maxWeightQueueWeight = 0;
    maxWeightQueueAge = 0;
  }

  // note: we ignore the option lrsWeightLimitOnly() if weightRatio is set to 0
  // TODO: force in Options that weightRatio is positive if lrsWeightLimitOnly() is set to 'on'.
  if (_opt.lrsWeightLimitOnly() && _weightRatio > 0)
  {
    // if the option lrsWeightLimitOnly() is set, we want to discard all clauses which are too heavy, regardless of the age.
    // we therefore make sure that fulfilsAgeLimit() always fails.
    maxAgeQueueAge = 0;
    maxAgeQueueWeight = 0;
  }

  return setLimits(maxAgeQueueAge, maxAgeQueueWeight,maxWeightQueueWeight, maxWeightQueueAge);
}

bool AWPassiveClauseContainer::childrenPotentiallyFulfilLimits(Clause* cl, unsigned upperBoundNumSelLits) const
{
  CALL("AWPassiveClauseContainer::childrenPotentiallyFulfilLimits");
  if (cl->age() == _ageSelectionMaxAge)
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
    if (!fulfilsWeightLimit(weightLowerBound, numPositiveLiteralsLowerBound, inf)) {
      //and also over weight limit
      return false;
    }
  }
  return true;
}

bool AWPassiveClauseContainer::setLimits(unsigned newAgeSelectionMaxAge, unsigned newAgeSelectionMaxWeight, unsigned newWeightSelectionMaxWeight, unsigned newWeightSelectionMaxAge)
{
  CALL("AWPassiveClauseContainer::setLimits");

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
  if(newWeightSelectionMaxWeight != _weightSelectionMaxWeight || newWeightSelectionMaxAge != _weightSelectionMaxAge) {
    if(newWeightSelectionMaxWeight < _weightSelectionMaxWeight) {
      atLeastOneTightened = true;
    } else if (newWeightSelectionMaxWeight == _weightSelectionMaxWeight && newWeightSelectionMaxAge < _weightSelectionMaxAge) {
      atLeastOneTightened = true;
    }
    _weightSelectionMaxWeight=newWeightSelectionMaxWeight;
    _weightSelectionMaxAge=newWeightSelectionMaxAge;
  }
  return atLeastOneTightened;
}

bool AWPassiveClauseContainer::ageLimited() const
{
  CALL("AWPassiveClauseContainer::ageLimited");

  return _ageRatio > 0 && _ageSelectionMaxAge != UINT_MAX && _ageSelectionMaxWeight != UINT_MAX;
}

bool AWPassiveClauseContainer::weightLimited() const
{
  CALL("AWPassiveClauseContainer::weightLimited");
  return _weightRatio > 0 && _weightSelectionMaxWeight != UINT_MAX && _weightSelectionMaxAge != UINT_MAX;
}

bool AWPassiveClauseContainer::fulfilsAgeLimit(Clause* cl) const
{
  CALL("AWPassiveClauseContainer::fulfilsAgeLimit(Clause*)");

  // don't want to reuse fulfilsAgeLimit(unsigned age,..) here, since we don't want to recompute weightForClauseSelection
  unsigned age = cl->age();
  unsigned weightForClauseSelection = cl->weightForClauseSelection(_opt);
  return age <= _ageSelectionMaxAge || (age == _ageSelectionMaxAge && weightForClauseSelection <= _ageSelectionMaxWeight);
}

bool AWPassiveClauseContainer::fulfilsAgeLimit(unsigned w, unsigned numPositiveLiterals, const Inference& inference) const
{
  CALL("AWPassiveClauseContainer::fulfilsAgeLimit(unsigned, unsigned, const Inference&)");

  const unsigned age = inference.age();
  const unsigned numeralWeight = 0; // heuristic: we don't want to compute the numeral weight during estimates and conservatively assume that it is 0.
  const unsigned splitWeight = 0; // also conservatively assuming 0
  /* In principle, we could compute this from the Inference (and it's not so expensive)
   * but it's only relevant with avatar on (and avatar would later compute the splitset of the new clause again)
   * and nonliteralsInClauseWeight on, which is not the default. So keeping the cheap version for now.
   */
  const bool derivedFromGoal = inference.derivedFromGoal();
  // If the caller was too lazy to supply an Inference object we conservatively assume that the result is a goal-clause.
  unsigned weightForClauseSelection = Clause::computeWeightForClauseSelection(w, splitWeight, numeralWeight, derivedFromGoal, _opt);
  return age <= _ageSelectionMaxAge || (age == _ageSelectionMaxAge && weightForClauseSelection <= _ageSelectionMaxWeight);
}

bool AWPassiveClauseContainer::fulfilsWeightLimit(Clause* cl) const
{
  CALL("AWPassiveClauseContainer::fulfilsWeightLimit(Clause*)");

  // don't want to reuse fulfilsWeightLimit(unsigned w,..) here, since we don't want to recompute weightForClauseSelection
  unsigned weightForClauseSelection = cl->weightForClauseSelection(_opt);
  unsigned age = cl->age();
  return weightForClauseSelection <= _weightSelectionMaxWeight || (weightForClauseSelection == _weightSelectionMaxWeight && age <= _weightSelectionMaxAge);
}

bool AWPassiveClauseContainer::fulfilsWeightLimit(unsigned w, unsigned numPositiveLiterals, const Inference& inference) const
{
  CALL("AWPassiveClauseContainer::fulfilsWeightLimit(unsigned, unsigned, const Inference&)");

  const unsigned age = inference.age();
  const unsigned numeralWeight = 0; // heuristic: we don't want to compute the numeral weight during estimates and conservatively assume that it is 0.
  const unsigned splitWeight = 0; // also conservatively assuming 0
  /* In principle, we could compute this from the Inference (and it's not so expensive)
   * but it's only relevant with avatar on (and avatar would later compute the splitset of the new clause again)
   * and nonliteralsInClauseWeight on, which is not the default. So keeping the cheap version for now.
   */
  const bool derivedFromGoal = inference.derivedFromGoal();
  // If the caller was too lazy to supply an Inference object we conservatively assume that the result is a goal-clause.
  unsigned weightForClauseSelection = Clause::computeWeightForClauseSelection(w, splitWeight, numeralWeight, derivedFromGoal, _opt);
  return weightForClauseSelection <= _weightSelectionMaxWeight || (weightForClauseSelection == _weightSelectionMaxWeight && age <= _weightSelectionMaxAge);
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

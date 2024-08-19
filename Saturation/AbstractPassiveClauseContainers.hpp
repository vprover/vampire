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
 * @file AbstractPassiveClauseContainers.hpp
 * Defines the class for PassiveClauseContainer construction
 * (based on queues) and their composition.
 * @since 31/12/2007 Manchester
 */

#ifndef __AbstractPassiveClauseContainers__
#define __AbstractPassiveClauseContainers__

namespace Saturation {

#include "Kernel/Clause.hpp"
#include "Kernel/ClauseQueue.hpp"

using namespace Kernel;

template<class T>
class SingleQueuePassiveClauseContainer : public PassiveClauseContainer {
protected:
  T _queue;
  unsigned _size;

public:
  SingleQueuePassiveClauseContainer(bool isOutermost, const Shell::Options& opt, std::string name)
    : PassiveClauseContainer(isOutermost, opt, name), _queue(opt), _size(0), _simulationIt(_queue) {}

  ~SingleQueuePassiveClauseContainer() {
    ClauseQueue::Iterator cit(_queue);
    while (cit.hasNext()) {
      Clause* cl=cit.next();
      ASS(!_isOutermost || cl->store()==Clause::PASSIVE);
      cl->setStore(Clause::NONE);
    }
  }

  void add(Clause* cl) override {
    ASS(cl->store() == Clause::PASSIVE);
    _queue.insert(cl);
    _size++;
    if (_isOutermost) {
      addedEvent.fire(cl);
    }
  }

  void remove(Clause* cl) override {
    if (_isOutermost) {
      ASS(cl->store()==Clause::PASSIVE);
    }
    if (_queue.remove(cl)) {
      _size--;
    }
    if (_isOutermost) {
      removedEvent.fire(cl);
      ASS(cl->store()!=Clause::PASSIVE);
    }
  }

  Clause* popSelected() override {
    ASS(!isEmpty());
    _size--;
    Clause* cl = _queue.pop();
    if (_isOutermost) {
      selectedEvent.fire(cl);
    }
    return cl;
  }

  /** True if there are no passive clauses */
  bool isEmpty() const override { return _queue.isEmpty(); }
  unsigned sizeEstimate() const override { return _size; }

  /*
   * LRS specific methods and fields for computation of Limits
   */
protected:
  ClauseQueue::Iterator _simulationIt;
  static constexpr T::OrdVal MAX_LIMIT = T::maxOrdVal();
  T::OrdVal _curLimit = MAX_LIMIT;

  bool setLimit(T::OrdVal newLimit) {
    bool thighened = newLimit < _curLimit;
    _curLimit = newLimit;
    return thighened;
  }
  bool exceedsLimit(Clause* cl) const {
    return _curLimit < _queue.getOrdVal(cl);
  }

public:
  void simulationInit() override {
    _simulationIt = ClauseQueue::Iterator(_queue);
  }

  bool simulationHasNext() override {
    return _simulationIt.hasNext();
  }

  void simulationPopSelected() override {
    _simulationIt.next();
  }

  // returns whether at least one of the limits was tightened
  bool setLimitsToMax() override {
    return setLimit(MAX_LIMIT);
  }

  // returns whether at least one of the limits was tightened
  bool setLimitsFromSimulation() override {
    if (_simulationIt.hasNext()) {
      return setLimit(_queue.getOrdVal(_simulationIt.next()));
    } else {
      return setLimitsToMax();
    }
  }

  void onLimitsUpdated() override {
    Recycled<Stack<Clause*>> toRemove;
    simulationInit(); // abused to setup fresh _simulationIt
    while (_simulationIt.hasNext()) {
      Clause* cl = _simulationIt.next();
      if (exceedsLimit(cl)) {
        toRemove.push(cl);
      }
    }
    while (toRemove.isNonEmpty()) {
      Clause* removed=toRemove.pop();
      RSTAT_CTR_INC("clauses discarded from passive on limit update");
      env.statistics->discardedNonRedundantClauses++;
      remove(removed);
    }
  }

  /*
   * LRS specific methods and fields for usage of limits
   */
public:
  // we don't know how to do this in general ...
  bool mayBeAbleToDiscriminateChildrenOnLimits() const override { return false; }
  // ... so this should not be called
  bool allChildrenNecessarilyExceedLimits(Clause* cl, unsigned upperBoundNumSelLits) const override { ASSERTION_VIOLATION; return false; }
  // we also don't know how to do this in general
  bool mayBeAbleToDiscriminateClausesUnderConstructionOnLimits() const override { return false; }

  // the following two are used in BinaryResolution and Superposition to terminate resulting clause construction early,
  // should it become clear that the final clause will not fulfill the current limits in the PassiveClauseContainer
  bool exceedsAgeLimit(unsigned w, unsigned numPositiveLiterals, const Inference& inference, bool& andThatsIt) const override { ASSERTION_VIOLATION; return false; }
  bool exceedsWeightLimit(unsigned w, unsigned numPositiveLiterals, const Inference& inference) const override { ASSERTION_VIOLATION; return false; }

  bool limitsActive() const override { return _curLimit != MAX_LIMIT; }
  bool exceedsAllLimits(Clause* c) const override { return limitsActive() && exceedsLimit(c); };
}; // class AgeBasedPassiveClauseContainer


};

#endif /* __AbstractPassiveClauseContainers__ */

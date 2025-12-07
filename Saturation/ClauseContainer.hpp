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
 * @file ClauseContainer.hpp
 * Defines class ClauseContainer
 *
 */

#ifndef __ClauseContainer__
#define __ClauseContainer__

#include "Forwards.hpp"

#include "Lib/Event.hpp"
#include "Lib/VirtualIterator.hpp"
#include "Lib/Deque.hpp"
#include "Kernel/Clause.hpp"
#include "Lib/Set.hpp"

#define OUTPUT_LRS_DETAILS 0

namespace Saturation
{

using namespace Lib;
using namespace Kernel;
using namespace Shell;

class ClauseContainer
{
  using ClauseEvent = SingleParamEvent<Clause *>;

public:
  virtual ~ClauseContainer() {}
  ClauseEvent addedEvent;
  /**
   * This event fires when a clause is removed from the
   * container because it is no longer needed, e.g. it was
   * backward-simplified, or the container is destroyed.
   * It does not fire for clauses that are removed from the
   * container because they are selected to be further
   * processed by the saturation algorithm (e.g. activated).
   */
  ClauseEvent removedEvent;
  /**
   * This event fires when a clause is removed from the
   * container to be further processed by the saturation
   * algorithm (e.g. activated).
   */
  ClauseEvent selectedEvent;
  virtual void add(Clause* c) = 0;
  void addClauses(ClauseIterator cit) {
    while (cit.hasNext()) {
      add(cit.next());
    }
  }
};

class RandomAccessClauseContainer
: public ClauseContainer
{
public:
  /**
   * Attach to the SaturationAlgorithm object.
   *
   * This method is being called in the SaturationAlgorithm constructor,
   * so no virtual methods of SaturationAlgorithm should be called.
   */
  void attach(SaturationAlgorithm* salg) {
    ASS(!_salg);
    _salg=salg;
  }

  /**
   * Detach from the SaturationAlgorithm object.
   *
   * This method is being called in the SaturationAlgorithm destructor,
   * so no virtual methods of SaturationAlgorithm should be called.
   */
  void detach() {
    ASS(_salg);
    _salg=0;
  }

  virtual unsigned sizeEstimate() const = 0;
  virtual void remove(Clause* c) = 0;

  void removeClauses(ClauseIterator cit) {
    while (cit.hasNext()) {
      remove(cit.next());
    }
  }

protected:
  RandomAccessClauseContainer() :_salg(0) {}
  SaturationAlgorithm* getSaturationAlgorithm() { return _salg; }
private:
  SaturationAlgorithm* _salg;
};

class PlainClauseContainer : public ClauseContainer {
public:
  void add(Clause* c) override
  {
    addedEvent.fire(c);
  }
};


class UnprocessedClauseContainer
: public ClauseContainer
{
public:
  ~UnprocessedClauseContainer() override;
  UnprocessedClauseContainer() : _data(64) {}
  void add(Clause* c) override;
  Clause* pop();
  bool isEmpty() const
  { return _data.isEmpty(); }
private:
  Deque<Clause*> _data;
};

typedef PlainEvent LimitsChangeEvent;

class PassiveClauseContainer
: public RandomAccessClauseContainer
{
public:
  PassiveClauseContainer(bool isOutermost, const Shell::Options& opt, std::string name = "") : _isOutermost(isOutermost), _opt(opt), _name(name) {}
  ~PassiveClauseContainer() override{};

  virtual bool isEmpty() const = 0;
  virtual Clause* popSelected() = 0;

  unsigned sizeEstimate() const override = 0;

  /*
   * LRS specific methods for computation of Limits
   */
  void updateLimits(long long estReachableCnt);

  virtual void simulationInit() = 0;
  virtual bool simulationHasNext() = 0;
  virtual void simulationPopSelected() = 0;

  // returns whether at least one of the limits was tightened
  virtual bool setLimitsToMax() = 0;
  // returns whether at least one of the limits was tightened
  virtual bool setLimitsFromSimulation() = 0;

  virtual void onLimitsUpdated() = 0;

  /*
   * LRS specific methods and fields for usage of limits
   */

  // it this is true, there is a chance that allChildrenNecessarilyExceedLimits will ever return true
  virtual bool mayBeAbleToDiscriminateChildrenOnLimits() const = 0;
  // given a clause cl and an upper bound on the number of selected literals in that clause and taking into account the current LRS limits,
  // this will return true whenever it can be esablished for cl that all its children necessirly exceed the limits
  virtual bool allChildrenNecessarilyExceedLimits(Clause* cl, unsigned upperBoundNumSelLits) const = 0;

  // it this is true, an inference may try to establish whether a clause under construction can be discarded early
  // by first checking, using exceedsAgeLimit(unsigned,unsigned,...), whether it exceeds the current ageLimit (if applicable)
  // and second checking, using exceedsWeightLimit(unsigned,unsigned,...) whether it exceeds the current weight (if applicable)
  virtual bool mayBeAbleToDiscriminateClausesUnderConstructionOnLimits() const = 0;

  // age is to be recovered from inference
  virtual bool exceedsAgeLimit(unsigned numPositiveLiterals, const Inference& inference, bool& andThatsIt) const = 0;
  // if age limit is all there is, the function sets andThatsIt to true (and the clause under construction can be discarded immediately)
  // if there is currently no weight limiting in place, yet the clause should later also be weight-limit-checked, the call to
  // mayBeAbleToDiscriminateClausesUnderConstructionOnLimits should have returned false already

  // note: w here denotes the weight as returned by weight().
  // age is to be recovered from inference
  // this method internally takes care of computing the corresponding weightForClauseSelection.
  virtual bool exceedsWeightLimit(unsigned w, unsigned numPositiveLiterals, const Inference& inference) const = 0;

  // if limits are active, LRS checks more frequently what the reachables are
  virtual bool limitsActive() const = 0;

  // The calls to exceedsAllLimits establishes (in the SaturationAlgorithm) if the newly derived clause should be discarded.
  // (The method is called exceedsAllLimits, because if we alternate between more than one queue, such as with awr,
  // all queues must agree that a clause is discardable, before that is done. In this regards, LRS is conservative.)
  virtual bool exceedsAllLimits(Clause* c) const = 0;
protected:
  bool _isOutermost;
  const Shell::Options& _opt;

public:
  std::string _name;
};

class ActiveClauseContainer
: public RandomAccessClauseContainer
{
public:
  ActiveClauseContainer() {}

  void add(Clause* c) override;
  void remove(Clause* c) override;

  unsigned sizeEstimate() const override { return _clauses.size(); }
  ClauseIterator clauses() const { return pvi(_clauses.iter()); }

protected:
  friend PassiveClauseContainer;
  void onLimitsUpdated(PassiveClauseContainer* limits);
private:
  Set<Clause*> _clauses;
  // const Shell::Options& _opt;
};


};

#endif /*__ClauseContainer__*/


/*
 * File AWPassiveClauseContainer.hpp.
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
 * @file AWPassiveClauseContainer.hpp
 * Defines the class AWPassiveClauseContainer
 * @since 31/12/2007 Manchester
 */

#ifndef __AWPassiveClauseContainer__
#define __AWPassiveClauseContainer__

#include <memory>
#include <vector>
#include "Lib/Comparison.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/ClauseQueue.hpp"
#include "ClauseContainer.hpp"

#include "Lib/Allocator.hpp"

namespace Saturation {

using namespace Kernel;

class AgeQueue
: public ClauseQueue
{
public:
  AgeQueue(const Options& opt) : _opt(opt) {}
protected:

  virtual bool lessThan(Clause*,Clause*);

  friend class AWPassiveClauseContainer;

private:
  const Shell::Options& _opt;
};

class WeightQueue
  : public ClauseQueue
{
public:
  WeightQueue(const Options& opt) : _opt(opt) {}
protected:
  virtual bool lessThan(Clause*,Clause*);

  friend class AWPassiveClauseContainer;
private:
  const Shell::Options& _opt;
};

class NeuralLogitsQueue
  : public ClauseQueue
{
protected:
  virtual bool lessThan(Clause* c1, Clause* c2) {
    if (c1->modelSaid() < c2->modelSaid())
      return true;

    if (c1->modelSaid() > c2->modelSaid())
      return false;

    return c1->number() < c2->number();
  }
};

class NeuralPrioQueue
  : public ClauseQueue
{
protected:
  virtual bool lessThan(Clause* c1, Clause* c2) {
    bool c1modelSaidYes = (c1->modelSaid() <= 0.0);
    bool c2modelSaidYes = (c2->modelSaid() <= 0.0);

    if (c1modelSaidYes && !c2modelSaidYes)
      return true;

    if (!c1modelSaidYes && c2modelSaidYes)
      return false;

    return c1->number() < c2->number();
  }
};

/**
 * A class to be used by the neural experiments.
 *
 * Currently implemented without LRS support.
 *
 * In the long term, AWPassiveClauseContainer should be implementable
 * as a (binary) meta-container out of two template-instances of this class.
 *
 **/
template <class QueueType>
class SingleQueuePassiveClauseContainer
    : public PassiveClauseContainer
{
public:
  CLASS_NAME(SingleQueuePassiveClauseContainer);
  USE_ALLOCATOR(SingleQueuePassiveClauseContainer);

  SingleQueuePassiveClauseContainer(bool isOutermost, const Shell::Options& opt, vstring name) :
    PassiveClauseContainer(isOutermost, opt, name) {}

  ~SingleQueuePassiveClauseContainer() override {
    CALL("SingleQueuePassiveClauseContainer::~SingleQueuePassiveClauseContainer");
    ClauseQueue::Iterator cit(_myQueue);
    while (cit.hasNext())
    {
      Clause* cl=cit.next();
      ASS(!_isOutermost || cl->store()==Clause::PASSIVE);
      cl->setStore(Clause::NONE);
    }
  }

  void add(Clause* cl) override {
    CALL("SingleQueuePassiveClauseContainer::add");
    ASS(cl->store() == Clause::PASSIVE);
    _myQueue.insert(cl);
    _size++;
    if (_isOutermost)
    {
      addedEvent.fire(cl);
    }
  }

  void remove(Clause* cl) override {
    CALL("SingleQueuePassiveClauseContainer::remove");
    if (_isOutermost)
    {
      ASS(cl->store()==Clause::PASSIVE);
    }
    bool wasRemoved = _myQueue.remove(cl);
    if (wasRemoved) {
      _size--;
    }
    if (_isOutermost)
    {
      removedEvent.fire(cl);
      ASS(cl->store()!=Clause::PASSIVE);
    }
  }

  Clause* popSelected() override {
    CALL("SingleQueuePassiveClauseContainer::popSelected");
    ASS(!isEmpty());
    _size--;

    Clause* cl = _myQueue.pop();

    if (_isOutermost) {
      selectedEvent.fire(cl);
    }

    return cl;
  }

  bool isEmpty() const override { return _myQueue.isEmpty(); }
  unsigned sizeEstimate() const override { return _size; }

protected:
  QueueType _myQueue;
  unsigned _size;
public:
  // brutally ignoring the LRS stuff
  void simulationInit() override {}
  bool simulationHasNext() override { return false; }
  void simulationPopSelected() override {}
  bool setLimitsToMax() override { return false; }
  bool setLimitsFromSimulation() override { return false; }
  void onLimitsUpdated() override {}

  bool ageLimited() const override { return false; }
  bool weightLimited() const override { return false; }
  bool fulfilsAgeLimit(Clause* c) const override { return true; }
  bool fulfilsAgeLimit(unsigned w, unsigned numPositiveLiterals, const Inference& inference) const override { return true; }
  bool fulfilsWeightLimit(Clause* cl) const override { return true; }
  bool fulfilsWeightLimit(unsigned w, unsigned numPositiveLiterals, const Inference& inference) const override { return true; }
  bool childrenPotentiallyFulfilLimits(Clause* cl, unsigned upperBoundNumSelLits) const override { return true; }
};

template <class QueueType>
class DelayedEvalSingleQueuePassiveClauseContainer
    : public SingleQueuePassiveClauseContainer<QueueType>
{
public:
  CLASS_NAME(DelayedEvalSingleQueuePassiveClauseContainer);
  USE_ALLOCATOR(DelayedEvalSingleQueuePassiveClauseContainer);

  DelayedEvalSingleQueuePassiveClauseContainer(bool isOutermost, const Shell::Options& opt, vstring name,void (*de)(Clause* cl)) :
    SingleQueuePassiveClauseContainer<QueueType>(isOutermost, opt, name), _delayedEvaluator(de) {}

  using SingleQueuePassiveClauseContainer<QueueType>::isEmpty;
  using SingleQueuePassiveClauseContainer<QueueType>::_myQueue;
  using SingleQueuePassiveClauseContainer<QueueType>::_size;
  using SingleQueuePassiveClauseContainer<QueueType>::_isOutermost;
  using SingleQueuePassiveClauseContainer<QueueType>::selectedEvent;

  Clause* popSelected() override {
    CALL("DelayedEvalSingleQueuePassiveClauseContainer::popSelected");
    ASS(!isEmpty());

    Clause* cl = _myQueue.pop();
    while (!cl->evalauted()) {
      _delayedEvaluator(cl);

      //cout << "Evaluated " << cl->toString() << endl;

      // This shortcut only reasoably works in combination with NeuralLogitsQueue
      if (cl->modelSaid() <= 0.0) {
        break;
      }

      _myQueue.insert(cl);
      cl = _myQueue.pop();
    }

    //cout << "Popping: " << cl->toString() << endl;

    _size--;
    if (_isOutermost) {
      selectedEvent.fire(cl);
    }

    return cl;
  }
private:
  void (*_delayedEvaluator)(Clause* cl);
};


/**
 * Defines the class Passive of passive clauses
 * @since 31/12/2007 Manchester
 */
class AWPassiveClauseContainer
: public PassiveClauseContainer
{
public:
  CLASS_NAME(AWPassiveClauseContainer);
  USE_ALLOCATOR(AWPassiveClauseContainer);

  AWPassiveClauseContainer(bool isOutermost, const Shell::Options& opt, vstring name);
  ~AWPassiveClauseContainer();
  void add(Clause* cl) override;

  void remove(Clause* cl) override;

  bool byWeight(int balance);

  Clause* popSelected() override;
  /** True if there are no passive clauses */
  bool isEmpty() const override
  { return _ageQueue.isEmpty() && _weightQueue.isEmpty(); }

  unsigned sizeEstimate() const override { return _size; }

  static Comparison compareWeight(Clause* cl1, Clause* cl2, const Shell::Options& opt);

private:
  /** The age queue, empty if _ageRatio=0 */
  AgeQueue _ageQueue;
  /** The weight queue, empty if _weightRatio=0 */
  WeightQueue _weightQueue;
  /** the age ratio */
  int _ageRatio;
  /** the weight ratio */
  int _weightRatio;
  /** current balance. If &lt;0 then selection by age, if &gt;0
   * then by weight */
  int _balance;
  /** Experimental: if set to true by an option, we use randomization instead of _balance to determine the next clause's selection. */
  bool _randomize;

  unsigned _size;

  /*
   * LRS specific methods and fields for computation of Limits
   */
public:
  void simulationInit() override;
  bool simulationHasNext() override;
  void simulationPopSelected() override;

  // returns whether at least one of the limits was tightened
  bool setLimitsToMax() override;
  // returns whether at least one of the limits was tightened
  bool setLimitsFromSimulation() override;

  void onLimitsUpdated() override;
private:
  bool setLimits(unsigned newAgeSelectionMaxAge, unsigned newAgeSelectionMaxWeight, unsigned newWeightSelectionMaxWeight, unsigned newWeightSelectionMaxAge);

  int _simulationBalance;
  ClauseQueue::Iterator _simulationCurrAgeIt;
  ClauseQueue::Iterator _simulationCurrWeightIt;
  Clause* _simulationCurrAgeCl;
  Clause* _simulationCurrWeightCl;

  unsigned _ageSelectionMaxAge;
  unsigned _ageSelectionMaxWeight;
  unsigned _weightSelectionMaxWeight;
  unsigned _weightSelectionMaxAge;

  /*
   * LRS specific methods and fields for usage of limits
   */
public:
  bool ageLimited() const override;
  bool weightLimited() const override;

  bool fulfilsAgeLimit(Clause* c) const override;
  // note: w here denotes the weight as returned by weight().
  // age is to be recovered from inference
  // this method internally takes care of computing the corresponding weightForClauseSelection.
  bool fulfilsAgeLimit(unsigned w, unsigned numPositiveLiterals, const Inference& inference) const override;
  bool fulfilsWeightLimit(Clause* cl) const override;
  // note: w here denotes the weight as returned by weight().
  // age is to be recovered from inference
  // this method internally takes care of computing the corresponding weightForClauseSelection.
  bool fulfilsWeightLimit(unsigned w, unsigned numPositiveLiterals, const Inference& inference) const override;

  bool childrenPotentiallyFulfilLimits(Clause* cl, unsigned upperBoundNumSelLits) const override;
  
}; // class AWPassiveClauseContainer

/**
 * Light-weight version of the AWPassiveClauseContainer that
 * is not linked to the SaturationAlgorithm
 */
class AWClauseContainer: public ClauseContainer
{
public:
  AWClauseContainer(const Shell::Options& opt);

  void add(Clause* cl);
  bool remove(Clause* cl);

  /**
   * Set age-weight ratio
   * @since 08/01/2008 flight Murcia-Manchester
   */
  void setAgeWeightRatio(int age,int weight)
  {
    ASS(age >= 0);
    ASS(weight >= 0);
    ASS(age > 0 || weight > 0);

    _ageRatio = age;
    _weightRatio = weight;
  }

  Clause* popSelected();
  /** True if there are no passive clauses */
  bool isEmpty() const;

  unsigned size() const { return _size; }

  static Comparison compareWeight(Clause* cl1, Clause* cl2);

private:
  /** The age queue, empty if _ageRatio=0 */
  AgeQueue _ageQueue;
  /** The weight queue, empty if _weightRatio=0 */
  WeightQueue _weightQueue;
  /** the age ratio */
  int _ageRatio;
  /** the weight ratio */
  int _weightRatio;
  /** current balance. If &lt;0 then selection by age, if &gt;0
   * then by weight */
  int _balance;

  unsigned _size;
};


};

#endif /* __AWPassiveClauseContainer__ */

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

#include "Lib/Random.hpp"
#include <torch/script.h>

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

/**
 * 
 * 
 */
class NeuralPassiveClauseContainer
: public PassiveClauseContainer
{
public:
  CLASS_NAME(NeuralPassiveClauseContainer);
  USE_ALLOCATOR(NeuralPassiveClauseContainer);

  NeuralPassiveClauseContainer(bool isOutermost, const Shell::Options& opt);
  virtual ~NeuralPassiveClauseContainer(){}

  unsigned sizeEstimate() const override { return _clauses.size(); }
  bool isEmpty() const override { return _clauses.size() == 0; } 
  void add(Clause* cl) override { 
    CALL("NeuralPassiveClauseContainer::add");
    ASS(cl->store() == Clause::PASSIVE);
    ALWAYS(_clauses.insert(cl)); 
    addedEvent.fire(cl); 
  }
  void remove(Clause* cl) override { 
    CALL("NeuralPassiveClauseContainer::remove");
    ASS(cl->store()==Clause::PASSIVE);
    ALWAYS(_clauses.remove(cl));
    removedEvent.fire(cl); 
    ASS(cl->store()!=Clause::PASSIVE);
  }
  Clause* popSelected() override { 
    CALL("NeuralPassiveClauseContainer::popSelected");
    ASS(_clauses.size());

    unsigned i = Random::getInteger(_clauses.size());
    decltype(_clauses)::Iterator it(_clauses);

    Clause *cl;
    while (it.hasNext()) {
      cl = it.next();
      if (i-- == 0) {
        break;
      }
    }

    _clauses.remove(cl); 
    selectedEvent.fire(cl); 

    return cl;
  }
private:
  Set<Clause*> _clauses;
  torch::jit::script::Module _model;

  /*
   * LRS specific methods for computation of Limits
   */
public:
  void simulationInit() override { NOT_IMPLEMENTED; }
  bool simulationHasNext() override { return false; }
  void simulationPopSelected() override { NOT_IMPLEMENTED; }

  // returns whether at least one of the limits was tightened
  bool setLimitsToMax() override { return false; }
  // returns whether at least one of the limits was tightened
  bool setLimitsFromSimulation() override { return false; }

  void onLimitsUpdated() override { NOT_IMPLEMENTED; }

  /*
   * LRS specific methods and fields for usage of limits
   */
  bool ageLimited() const override { return false; }
  bool weightLimited() const override { return false; }

  bool fulfilsAgeLimit(Clause* c) const override { return true; }
  // note: w here denotes the weight as returned by weight().
  // this method internally takes care of computing the corresponding weightForClauseSelection.

  bool fulfilsAgeLimit(unsigned w, unsigned numPositiveLiterals, const Inference& inference) const override { return true; }
  bool fulfilsWeightLimit(Clause* cl) const override { return true; }
  // note: w here denotes the weight as returned by weight().
  // this method internally takes care of computing the corresponding weightForClauseSelection.
  bool fulfilsWeightLimit(unsigned w, unsigned numPositiveLiterals, const Inference& inference) const override { return true; }

  bool childrenPotentiallyFulfilLimits(Clause* cl, unsigned upperBoundNumSelLits) const override { return true; }  
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

  bool _randomized;
};


};

#endif /* __AWPassiveClauseContainer__ */

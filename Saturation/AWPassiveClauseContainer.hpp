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
 * Defines the class Passive of passive clauses
 * @since 31/12/2007 Manchester
 */
class AWPassiveClauseContainer
: public PassiveClauseContainer
{
public:
  AWPassiveClauseContainer(bool isOutermost, const Shell::Options& opt, std::string name);
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
  bool setLimits(unsigned newAgeSelectionMaxAge, unsigned newAgeSelectionMaxWeight, unsigned newWeightSelectionMaxWeight);

  int _simulationBalance;
  ClauseQueue::Iterator _simulationCurrAgeIt;
  ClauseQueue::Iterator _simulationCurrWeightIt;
  Clause* _simulationCurrAgeCl;
  Clause* _simulationCurrWeightCl;

  unsigned _ageSelectionMaxAge;
  unsigned _ageSelectionMaxWeight;
  unsigned _weightSelectionMaxWeight;
  // experiment showed that maintaining the tiebreaker _weightSelectionMaxAge
  // and doing the corresponding extra check (in fulfilsWeightLimit) didn't lead to a better performance
  // (possible explanation: it's better to be careful on the weight queue about age as "all small clauses, no matter how old/young are potentially usefull"
  // while at the same time, it's better to be more agressive with deletions on the age queue, as the large clauses there are probably useless)

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


};

#endif /* __AWPassiveClauseContainer__ */

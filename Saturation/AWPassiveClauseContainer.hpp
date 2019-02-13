
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
#include "Shell/Options.hpp"

#include "Lib/Allocator.hpp"

namespace Saturation {

using namespace Kernel;

class AgeQueue
: public ClauseQueue
{
public:
  AgeQueue(const Options& opt) : _opt(opt), _modelSaidYes(opt.modelSaidYes()) {}
protected:

  virtual bool lessThan(Clause*,Clause*);

  friend class AWPassiveClauseContainer;

private:
  const Shell::Options& _opt;
  bool _modelSaidYes;
};

class WeightQueue
  : public ClauseQueue
{
public:
  WeightQueue(const Options& opt) : _opt(opt), _modelSaidYes(opt.modelSaidYes()) {}
protected:
  virtual bool lessThan(Clause*,Clause*);

  friend class AWPassiveClauseContainer;
private:
  const Shell::Options& _opt;
  bool _modelSaidYes;
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
  virtual ~AWPassiveClauseContainer();
  void add(Clause* cl);

  void remove(Clause* cl);

  bool byWeight(int balance);

  Clause* popSelected();
  /** True if there are no passive clauses */
  bool isEmpty() const
  { return _ageQueue.isEmpty() && _weightQueue.isEmpty(); }

  virtual unsigned sizeEstimate() const { return _size; }

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
  virtual void simulationInit();
  virtual bool simulationHasNext();
  virtual void simulationPopSelected();

  // returns whether at least one of the limits was tightened
  virtual bool setLimitsToMax();
  // returns whether at least one of the limits was tightened
  virtual bool setLimitsFromSimulation();

  virtual void onLimitsUpdated();
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
  virtual bool ageLimited() const;
  virtual bool weightLimited() const;

  virtual bool fulfilsAgeLimit(Clause* c) const;
  // note: w here denotes the weight as returned by weight().
  // this method internally takes care of computing the corresponding weightForClauseSelection.
  virtual bool fulfilsAgeLimit(unsigned age, unsigned w, unsigned numeralWeight, bool derivedFromGoal, Inference* inference) const;
  virtual bool fulfilsWeightLimit(Clause* cl) const;
  // note: w here denotes the weight as returned by weight().
  // this method internally takes care of computing the corresponding weightForClauseSelection.
  virtual bool fulfilsWeightLimit(unsigned w, unsigned numeralWeight, bool derivedFromGoal, unsigned age, Inference* inference) const;

  virtual bool childrenPotentiallyFulfilLimits(Clause* cl, unsigned upperBoundNumSelLits) const;
  
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

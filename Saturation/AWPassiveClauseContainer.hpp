
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
  static bool theActualLessThen(Clause*,Clause*,const Options& opt);
protected:
  bool lessThan(Clause* cl1 ,Clause* cl2) override {
    return theActualLessThen(cl1,cl2,_opt);
  }

  friend class AWPassiveClauseContainer;

private:
  const Options& _opt;
};

class WeightQueue
  : public ClauseQueue
{
public:
  WeightQueue(const Options& opt) : _opt(opt) {}
  static bool theActualLessThen(Clause*,Clause*,const Options& opt);
protected:
  bool lessThan(Clause* cl1,Clause* cl2) override {
    return theActualLessThen(cl1,cl2,_opt);
  }

  friend class AWPassiveClauseContainer;
private:
  const Options& _opt;
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

  AWPassiveClauseContainer(const Options& opt);
  virtual ~AWPassiveClauseContainer();
  void add(Clause* cl);

  void remove(Clause* cl);

  bool byWeight();
  Clause* peekSelected();
  Clause* popSelected();
  /** True if there are no passive clauses */
  bool isEmpty() const
  { return _ageQueue.isEmpty() && _weightQueue.isEmpty(); }

  ClauseIterator iterator();

  void updateLimits(long long estReachableCnt);

  virtual unsigned size() const { return _size; }


  static Comparison compareWeight(Clause* cl1, Clause* cl2, const Options& opt);
protected:
  void onLimitsUpdated(LimitsChangeType change);
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

  const Options& _opt;
}; // class AWPassiveClauseContainer

class PredicateSplitPassiveClauseContainer
: public PassiveClauseContainer
{
public:
  CLASS_NAME(PredicateSplitPassiveClauseContainer);
  USE_ALLOCATOR(PredicateSplitPassiveClauseContainer);

  PredicateSplitPassiveClauseContainer(const Options& opt);
  virtual ~PredicateSplitPassiveClauseContainer() {}

  void add(Clause* cl);
  void remove(Clause* cl);
  Clause* popSelected();

  /** True if there are no passive clauses */
  bool isEmpty() const
  { return _yesPCC.isEmpty() && _noPCC.isEmpty(); }

  ClauseIterator iterator();

  void updateLimits(long long estReachableCnt) { /* TODO: the LRS stuff */}

  virtual unsigned size() const { return _yesPCC.size() + _noPCC.size(); }

protected:
  void onLimitsUpdated(LimitsChangeType change) { /* TODO: the LRS stuff */}

private:
  AWPassiveClauseContainer _yesPCC, _noPCC;

  int _yesRatio;
  int _noRatio;
  int _balance;
  const Options& _opt;
}; // class PredicateSplitPassiveClauseContainer


/**
 * Light-weight version of the AWPassiveClauseContainer that
 * is not linked to the SaturationAlgorithm
 */
class AWClauseContainer: public ClauseContainer
{
public:
  AWClauseContainer(const Options& opt);

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

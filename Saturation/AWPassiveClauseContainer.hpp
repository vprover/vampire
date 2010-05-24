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


namespace Saturation {

using namespace Kernel;

class AgeQueue
  : public ClauseQueue
{
protected:
  virtual bool lessThan(Clause*,Clause*);

  friend class AWPassiveClauseContainer;
};

class WeightQueue
  : public ClauseQueue
{
protected:
  virtual bool lessThan(Clause*,Clause*);

  friend class AWPassiveClauseContainer;
};

/**
 * Defines the class Passive of passive clauses
 * @since 31/12/2007 Manchester
 */
class AWPassiveClauseContainer:
public PassiveClauseContainer
{
public:
  AWPassiveClauseContainer();
  ~AWPassiveClauseContainer();
  void add(Clause* cl);

  void remove(Clause* cl);

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
  bool isEmpty() const
  { return _ageQueue.isEmpty() && _weightQueue.isEmpty(); }

  ClauseIterator iterator();

  void updateLimits(long long estReachableCnt);

  unsigned size() const { return _size; }

  void beforePassiveClauseUpdated(Clause* cl);
  void afterPassiveClauseUpdated(Clause* cl);


  static Comparison compareWeight(Clause* cl1, Clause* cl2);
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

  static int s_nwcNumerator;
  static int s_nwcDenominator;

  unsigned _size;
}; // class AWPassiveClauseContainer

};

#endif /* __AWPassiveClauseContainer__ */

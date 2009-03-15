/**
 * @file AWPassiveClauseContainer.hpp
 * Defines the class AWPassiveClauseContainer
 * @since 31/12/2007 Manchester
 */

#ifndef __AWPassiveClauseContainer__
#define __AWPassiveClauseContainer__

#include "../Kernel/Clause.hpp"
#include "../Kernel/ClauseQueue.hpp"
#include "ClauseContainer.hpp"


namespace Saturation {

using namespace Kernel;

class AgeQueue
  : public ClauseQueue
{
protected:
  virtual bool lessThan(Clause*,Clause*);
};

class WeightQueue
  : public ClauseQueue
{
protected:
  virtual bool lessThan(Clause*,Clause*);
};

/**
 * Defines the class Passive of passive clauses
 * @since 31/12/2007 Manchester
 */
class AWPassiveClauseContainer:
public PassiveClauseContainer
{
public:
  AWPassiveClauseContainer() : _balance(0) {};
  ~AWPassiveClauseContainer();
  void add(Clause* c);

  /**
   * Remove Clause from the Passive store. Should be called only
   * when the Clause is no longer needed by the inference process
   * (i.e. was backward subsumed/simplified), as it can result in
   * deletion of the clause.
   */
  void remove(Clause* c)
  {
    ASS_EQ(c->store(), Clause::PASSIVE);
    _ageQueue.remove(c);
    _weightQueue.remove(c);
    removedEvent.fire(c);
    c->setStore(Clause::NONE);
  }

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

  void updateLimits(long estReachableCnt);

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
}; // class AWPassiveClauseContainer

};

#endif /* __AWPassiveClauseContainer__ */

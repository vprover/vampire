/**
 * @file Passive.hpp
 * Defines the class Passive of passive clauses
 * @since 31/12/2007 Manchester
 */

#ifndef __Passive__
#define __Passive__

#include "../Kernel/ClauseQueue.hpp"

using namespace Kernel;

namespace Resolution {

class AgeQueue
  : public ClauseQueue
{
protected:
  virtual bool lessThan(const Clause*,const Clause*);
};

class WeightQueue
  : public ClauseQueue
{
protected:
  virtual bool lessThan(const Clause*,const Clause*);
};

/**
 * Defines the class Passive of passive clauses
 * @since 31/12/2007 Manchester
 */
class Passive
{
public:
  void add(Clause& c);
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
  Clause* select();
  /** True if there are no passive clauses */
  bool isEmpty() const
  { return _ageRatio ? _ageQueue.isEmpty() : _weightQueue.isEmpty(); }
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
}; // class Passive

}

#endif

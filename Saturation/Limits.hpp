/**
 * @file Limits.hpp
 * Defines class Limits
 *
 */

#ifndef __Limits__
#define __Limits__

#include "../Forwards.hpp"

#include "../Lib/Event.hpp"

#include "../Kernel/Clause.hpp"


namespace Saturation
{

using namespace Lib;
using namespace Kernel;

enum LimitsChangeType {
  NO_LIMITS_CHANGE=0,
  LIMITS_TIGHTENED=1,
  LIMITS_LOOSENED=2,
  GENERAL_LIMITS_CHANGE=3
};

typedef SingleParamEvent<LimitsChangeType> LimitsChangeEvent;

class Limits
{
public:
  Limits() : _maxAge(-1), _maxWeight(-1) {}

  LimitsChangeEvent changedEvent;

  int ageLimit() { return _maxAge; }
  bool ageLimited() { return _maxAge!=-1; }

  int weightLimit() { return _maxWeight; }
  int nonGoalWeightLimit() { return _maxNonGoalWeight; }
  bool weightLimited() { return _maxWeight!=-1; }

  bool fulfillsLimits(Clause* cl)
  {
    if(!ageLimited() || !weightLimited()) {
      return true;
    }
    return (cl->age() <= ageLimit()) || (cl->getEffectiveWeight() <= weightLimit());
  }

  void setLimits(int newMaxAge, int newMaxWeight);

private:
  int _maxAge;
  int _maxWeight;
  int _maxNonGoalWeight;
};

};

#endif /*__Limits__*/

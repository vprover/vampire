/**
 * @file Limits.cpp
 * Implements class Limits.
 */

#include "Lib/Environment.hpp"

#include "Shell/Options.hpp"


#include "Limits.hpp"

namespace Saturation
{

bool Limits::fulfillsLimits(Clause* cl)
{
  CALL("Limits::fulfillsLimits");

  if(!ageLimited() || !weightLimited()) {
    return true;
  }
  return (cl->age() <= ageLimit()) || (cl->getEffectiveWeight(_opt) <= weightLimit());
}

void Limits::setLimits(int newMaxAge, int newMaxWeight)
{
  CALL("Limits::setLimits");
  ASS_GE(newMaxAge,-1);
  ASS_GE(newMaxWeight,-1);

  LimitsChangeType res=NO_LIMITS_CHANGE;
  if(_maxAge!=newMaxAge) {
    if(_maxAge==-1||_maxAge>newMaxAge) {
	res=static_cast<LimitsChangeType>(res|LIMITS_TIGHTENED);
    } else {
	res=static_cast<LimitsChangeType>(res|LIMITS_LOOSENED);
    }
    _maxAge=newMaxAge;
  }
  if(_maxWeight!=newMaxWeight) {
    if(_maxWeight==-1||_maxWeight>newMaxWeight) {
	res=static_cast<LimitsChangeType>(res|LIMITS_TIGHTENED);
    } else {
	res=static_cast<LimitsChangeType>(res|LIMITS_LOOSENED);
    }
    _maxWeight=newMaxWeight;
    if(_maxWeight==-1) {
	_maxNonGoalWeight=-1;
    } else {
	_maxNonGoalWeight=static_cast<int>(_maxWeight/_opt.nongoalWeightCoefficient());
    }
  }
  if(res!=NO_LIMITS_CHANGE) {
    changedEvent.fire(res);
  }
}


}

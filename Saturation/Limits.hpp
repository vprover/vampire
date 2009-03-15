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
  bool weightLimited() { return _maxWeight!=-1; }

  bool fulfillsLimits(Clause* cl)
  {
    if(!ageLimited() || !weightLimited()) {
      return true;
    }
    return (cl->weight() <= weightLimit()) || (cl->age() <= ageLimit());
  }

  void setLimits(int newMaxAge, int newMaxWeight)
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
    }
    if(res!=NO_LIMITS_CHANGE) {
      changedEvent.fire(res);
    }
  }
private:
  int _maxAge;
  int _maxWeight;
};

};

#endif /*__Limits__*/

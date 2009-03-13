/**
 * @file Limits.hpp
 * Defines class Limits
 *
 */

#ifndef __Limits__
#define __Limits__

#include "../Forwards.hpp"

#include "../Lib/Event.hpp"


namespace Saturation
{

using namespace Lib;

enum LimitsChangeType {
  LIMITS_TIGHTENED=0,
  LIMITS_LOOSENED=1,
  GENERAL_LIMITS_CHANGE=2
};

typedef SingleParamEvent<LimitsChangeType> LimitsChangeEvent;

class Limits
{
public:
  LimitsChangeEvent changedEvent;

  unsigned ageLimit() { return _maxAge; }
  bool ageLimited() { return _maxAge!=-1; }

  unsigned weightLimit() { return _maxWeight; }
  bool weightLimited() { return _maxWeight!=-1; }

private:
  int _maxAge;
  int _maxWeight;
};

};

#endif /*__Limits__*/

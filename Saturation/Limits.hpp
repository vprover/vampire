
/*
 * File Limits.hpp.
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
 * @file Limits.hpp
 * Defines class Limits
 *
 */

#ifndef __Limits__
#define __Limits__

#include "Forwards.hpp"

#include "Lib/Event.hpp"

#include "Kernel/Clause.hpp"


namespace Saturation
{

using namespace Lib;
using namespace Kernel;
using namespace Shell;

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
  Limits(const Options& opt) : _maxAge(-1), _maxWeight(-1), _opt(opt) {}

  LimitsChangeEvent changedEvent;

  unsigned ageLimit() { return _maxAge; }                       // implicit cast will turn -1 to UINT_MAX, which may be intended
  bool ageLimited() { return _maxAge!=-1; }

  unsigned weightLimit() { return _maxWeight; }                 // implicit cast will turn -1 to UINT_MAX, which may be intended
  unsigned nonGoalWeightLimit() { return _maxNonGoalWeight; }   // implicit cast will turn -1 to UINT_MAX, which may be intended
  bool weightLimited() { return _maxWeight!=-1; }

  bool fulfillsLimits(Clause* cl);

  void setLimits(int newMaxAge, int newMaxWeight,bool initial=false);

private:
  int _maxAge;
  int _maxWeight;
  int _maxNonGoalWeight;
  const Options& _opt;
};

};

#endif /*__Limits__*/

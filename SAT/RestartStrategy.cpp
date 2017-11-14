
/*
 * File RestartStrategy.cpp.
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
 * @file RestartStrategy.cpp
 * Implements class RestartStrategy.
 */

#include <math.h>

#include "Debug/Assertion.hpp"
#include "Debug/Tracer.hpp"

#include "RestartStrategy.hpp"

namespace SAT
{

size_t RestartStrategy::increase(size_t val, float quotient)
{
  return static_cast<size_t>(ceilf(val*quotient));
}

size_t GeometricRestartStrategy::getNextConflictCount()
{
  CALL("GeometricRestartStrategy::getNextConflictCount");

  size_t res = _conflictCnt;
  _conflictCnt = increase(_conflictCnt,_increase);
  return res;
}


/**
 * Return @c i -th Luby number
 *
 * The algorithm is based on
 * http://www.satcompetition.org/gorydetails/?p=3
 */
size_t LubyRestartStrategy::getLubyNumber(size_t i)
{
  CALL("LubyRestartStrategy::getLubyNumber");
  ASS_G(i,0);

  /* let 2^k be the least power of 2 >= (i+1) */
  size_t k = 1;
  size_t power = 2;
  while (power < (i + 1)) {
      k += 1;
      power *= 2;
  }
  if (power == (i + 1)) {
    return (power / 2);
  }
  return (getLubyNumber(i - (power / 2) + 1));
}

size_t MinisatRestartStrategy::getNextConflictCount()
{
  CALL("MinisatRestartStrategy::getNextConflictCount");

  if(_innerCnt>=_outerCnt) {
    _outerCnt = increase(_outerCnt,_increase);
    _innerCnt = _initConflictCnt;
  }
  else {
    _innerCnt = increase(_innerCnt,_increase);
  }
  return _innerCnt;
}


}

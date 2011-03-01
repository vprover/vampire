/**
 * @file RestartStrategy.cpp
 * Implements class RestartStrategy.
 */

#include <math.h>

#include "Debug/Assertion.hpp"

#include "RestartStrategy.hpp"

namespace SAT
{

size_t GeometricRestartStrategy::getNextConflictCount()
{
  CALL("GeometricRestartStrategy::getNextConflictCount");

  size_t res = _conflictCnt;
  _conflictCnt = static_cast<size_t>(ceilf(_conflictCnt*_increase));
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

}

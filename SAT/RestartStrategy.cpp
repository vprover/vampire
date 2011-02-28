/**
 * @file RestartStrategy.cpp
 * Implements class RestartStrategy.
 */

#include <math.h>

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


}

/**
 * @file SaturationAlgorithm.cpp
 * Implementing SaturationResult struct.
 */

#include "Kernel/Clause.hpp"
#include "SaturationResult.hpp"

using namespace Saturation;

void SaturationResult::updateStatistics()
{
  env.statistics->terminationReason=terminationReason;
  env.statistics->refutation=refutation;
}

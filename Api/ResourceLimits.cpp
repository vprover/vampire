/**
 * @file ResourceLimits.cpp
 * Implements class ResourceLimits.
 */

#include "ResourceLimits.hpp"

#include "Debug/Assertion.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/Environment.hpp"

#include "Shell/Options.hpp"

namespace Api
{

void ResourceLimits::setLimits(size_t memoryInBytes, int timeInDeciseconds)
{
  CALL("ResourceLimits::setLimits");

  env.options->setMemoryLimit(memoryInBytes);
  Allocator::setMemoryLimit(memoryInBytes);

  env.options->setTimeLimitInDeciseconds(timeInDeciseconds);
}

}

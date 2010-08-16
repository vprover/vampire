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

#ifdef VAPI_LIBRARY

//here we ensure that if Vampire is used as a library, we do not impose
//any time or memory limit by default

struct InitHelper
{
  InitHelper()
  {
    ResourceLimits::disableLimits();
  }
};

InitHelper initializerAuxObject;

#endif

void ResourceLimits::setLimits(size_t memoryInBytes, int timeInDeciseconds)
{
  CALL("ResourceLimits::setLimits");

  env.options->setMemoryLimit(memoryInBytes);
  Allocator::setMemoryLimit(memoryInBytes);

  env.options->setTimeLimitInDeciseconds(timeInDeciseconds);
}

}

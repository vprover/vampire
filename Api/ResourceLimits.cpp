/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file ResourceLimits.cpp
 * Implements class ResourceLimits.
 */

#include "ResourceLimits.hpp"

#include "Debug/Assertion.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/Environment.hpp"
#include "Lib/System.hpp"

#include "Shell/Options.hpp"

namespace Api
{

using namespace Lib;

//#ifdef VAPI_LIBRARY

//here we ensure that if Vampire is used as a library, we do not impose
//any time or memory limit by default

struct __InitHelper
{
  static void init()
  {
    ResourceLimits::disableLimits();

    env.options->setOutputAxiomNames(true);
  }

  __InitHelper()
  {
    System::addInitializationHandler(init,0);
  }
};

__InitHelper initializerAuxObject;

//#endif

void ResourceLimits::setLimits(size_t memoryInBytes, int timeInDeciseconds)
{
  CALL("ResourceLimits::setLimits");

  env.options->setMemoryLimit(memoryInBytes);
  Allocator::setMemoryLimit(memoryInBytes);

  env.options->setTimeLimitInDeciseconds(timeInDeciseconds);
}

}

/**
 * @file ResourceLimits.hpp
 * Defines class ResourceLimits.
 */

#ifndef __ResourceLimits__
#define __ResourceLimits__

#include <cstddef>

namespace Api {

class ResourceLimits
{
public:
  /**
   * Remove the time and memory limit
   */
  static void disableLimits()
  { setLimits(0,0); }
  /**
   * Set the time and memory limit, zero means unlimited.
   */
  static void setLimits(size_t memoryInBytes, int timeInDeciseconds);
};

}

#endif // __ResourceLimits__

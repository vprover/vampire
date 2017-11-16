
/*
 * File ResourceLimits.hpp.
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
 * @file ResourceLimits.hpp
 * Defines class ResourceLimits.
 */

#ifndef __API_ResourceLimits__
#define __API_ResourceLimits__

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

#endif // __API_ResourceLimits__

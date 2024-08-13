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
 * @file DistinctGroupExpansion.hpp
 * Defines expansion of distinct groups
 */

#ifndef __DistinctGroupExpansion__
#define __DistinctGroupExpansion__

#include "Forwards.hpp"

namespace Shell{

using namespace Kernel;

/**
 * Expands distinct groups if they meet certain criteria
 */
class DistinctGroupExpansion {
public:
  DistinctGroupExpansion(unsigned expandUpToSize) : _expandUpToSize(expandUpToSize) {}

  void apply(Problem& prb);
  bool apply(UnitList*& units);
  Formula* expand(Lib::Stack<unsigned>& constants);
private:
  unsigned _expandUpToSize;
};


}
#endif

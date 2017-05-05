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
  DistinctGroupExpansion(){}

  void apply(Problem& prb);
  bool apply(UnitList*& units);
  Formula* expand(Stack<unsigned>& constants);

};


}
#endif

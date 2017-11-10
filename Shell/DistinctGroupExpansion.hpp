
/*
 * File DistinctGroupExpansion.hpp.
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
  static const unsigned EXPAND_UP_TO_SIZE = 140;

  DistinctGroupExpansion(){}

  void apply(Problem& prb);
  bool apply(UnitList*& units);
  Formula* expand(Stack<unsigned>& constants);

};


}
#endif

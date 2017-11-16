
/*
 * File GeneralSplitting.hpp.
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
 * @file GeneralSplitting.hpp
 * Defines class GeneralSplitting.
 */


#ifndef __GeneralSplitting__
#define __GeneralSplitting__

#include "Forwards.hpp"

namespace Shell {

using namespace Kernel;

/**
 * Rule for splitting that reduces number of variables in a clause.
 */
class GeneralSplitting
{
public:
  void apply(Problem& prb);
  bool apply(UnitList*& units);
  bool apply(ClauseList*& units);
private:
  bool apply(Clause*& cl, UnitList*& resultStack);

};

};

#endif /* __GeneralSplitting__ */

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
 * @file Shuffling.hpp
 * Defines class Shuffling implementing the shuffling of the input.
 * @since 9/6/2021 Prague
 */

#ifndef __Shuffling__
#define __Shuffling__

#include "Forwards.hpp"

#include "Lib/Comparison.hpp"
#include "Kernel/Unit.hpp"

namespace Shell {

using namespace Lib;
using namespace Kernel;

/**
 * Class implementing shuffling-related procedures.
 * @since 09/06/2021 Prague
 */
class Shuffling
{
public:
  void shuffle(Problem&);
  UnitList* shuffle(UnitList*);
  Unit* shuffle(Unit*);

}; // class Shuffling

}

#endif

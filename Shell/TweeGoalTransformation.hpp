/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __TweeGoalTransformation__
#define __TweeGoalTransformation__

#include "Forwards.hpp"

namespace Shell {

class TweeGoalTransformation {
public:
  void apply(Kernel::Problem &, bool grounOnly);
};

};

#endif /* __TweeGoalTransformation__ */

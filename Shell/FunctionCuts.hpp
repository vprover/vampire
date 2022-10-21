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
 * @file FunctionCuts.hpp
 */

#ifndef __FunctionCuts__
#define __FunctionCuts__

#include "Forwards.hpp"

namespace Shell {

using namespace Kernel;

class FunctionCuts
{
public:
  static void apply(Kernel::Problem& prb);
};

}

#endif

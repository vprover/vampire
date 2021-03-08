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
 * @file ProvingHelper.hpp
 * Defines class ProvingHelper.
 */

#ifndef __ProvingHelper__
#define __ProvingHelper__

#include "Forwards.hpp"

namespace Saturation {

using namespace Kernel;
using namespace Shell;

class ProvingHelper {
public:
  static void runVampireSaturation(Problem& prb, const Options& opt);
  static void runVampire(Problem& prb, const Options& opt);
private:
  static void runVampireSaturationImpl(Problem& prb, const Options& opt);
};

}

#endif // __ProvingHelper__

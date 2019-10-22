
/*
 * File ProvingHelper.hpp.
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
  static void runVampireSaturation(Problem& prb, Options& opt);
  static void runVampire(Problem& prb, Options& opt);
private:
  static void runVampireSaturationImpl(Problem& prb, Options& opt);
};

}

#endif // __ProvingHelper__

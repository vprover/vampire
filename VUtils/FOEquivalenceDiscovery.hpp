
/*
 * File FOEquivalenceDiscovery.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file FOEquivalenceDiscovery.hpp
 * Defines class FOEquivalenceDiscovery.
 */

#ifndef __FOEquivalenceDiscovery__
#define __FOEquivalenceDiscovery__

#include "Forwards.hpp"



namespace VUtils {

using namespace Lib;
using namespace Kernel;
using namespace Shell;

class FOEquivalenceDiscovery {
public:
  int perform(int argc, char** argv);
private:
  vstring getArgStr(unsigned arity);
};

}

#endif // __FOEquivalenceDiscovery__

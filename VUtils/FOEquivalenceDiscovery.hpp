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

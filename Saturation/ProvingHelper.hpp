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
  static void runVampireSaturation(ClauseIterator clauses);
  static void runVampire(UnitList* units, Property* prop=0);
private:
  static void runVampireSaturationImpl(ClauseIterator clauses);
};

}

#endif // __ProvingHelper__

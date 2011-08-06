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
  static void runVampireSaturation(ClauseIterator clauses,Property* prop);
  static void runVampire(UnitList* units, Property* prop);
private:
  static void runVampireSaturationImpl(ClauseIterator clauses,Property* prop);
};

}

#endif // __ProvingHelper__

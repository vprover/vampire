/**
 * @file InputReader.hpp
 * Defines class InputReader.
 */

#ifndef __InputReader__
#define __InputReader__

#include "Forwards.hpp"

namespace Shell {

using namespace Lib;
using namespace Kernel;

class InputReader {
public:
  static UnitList* getUnits();
};

}

#endif // __InputReader__

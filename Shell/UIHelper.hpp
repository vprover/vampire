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

class UIHelper {
public:
  static UnitList* getInputUnits();

  static void outputResult();
};

}

#endif // __InputReader__

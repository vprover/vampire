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

  /**
   * Return true if there was a conjecture formula among the parsed units
   *
   * The purpose of this information is that when we report success in the
   * SZS ontology, we decide whether to output "Theorem" or "Unsatisfiable"
   * based on this value.
   */
  static bool haveConjecture() { return s_haveConjecture; }
  static bool cascMode;
private:
  static bool s_haveConjecture;
};

}

#endif // __InputReader__

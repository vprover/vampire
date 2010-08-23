/**
 * @file UIHelper.hpp
 * Defines class UIHelper.
 */

#ifndef __InputReader__
#define __InputReader__

#include <ostream>

#include "Forwards.hpp"

namespace Shell {

using namespace Lib;
using namespace Kernel;

class UIHelper {
public:
  static UnitList* getInputUnits();
  static void outputResult(ostream& out);

  /**
   * Return true if there was a conjecture formula among the parsed units
   *
   * The purpose of this information is that when we report success in the
   * SZS ontology, we decide whether to output "Theorem" or "Unsatisfiable"
   * based on this value.
   */
  static bool haveConjecture() { return s_haveConjecture; }
  static void setConjecturePresence(bool haveConjecture) { s_haveConjecture=haveConjecture; }

  /**
   * True if we are running in the CASC mode
   *
   * CASC mode means that we will output messages also in the SZS format.
   */
  static bool cascMode;
  /**
   * True if we are running in the CASC mode and we are the child process
   */
  static bool cascModeChild;
private:

  static bool s_haveConjecture;
};

}

#endif // __InputReader__

/**
 * @file InputReader.hpp
 * Defines class InputReader.
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
  static void runVampireSaturation(ClauseIterator clauses);
  static void runVampire(UnitList* units, Property* prop=0);
  static void outputResult(ostream& out);

  /**
   * Return true if there was a conjecture formula among the parsed units
   *
   * The purpose of this information is that when we report success in the
   * SZS ontology, we decide whether to output "Theorem" or "Unsatisfiable"
   * based on this value.
   */
  static bool haveConjecture() { return s_haveConjecture; }

  /**
   * True if we are running in a CASC mode
   *
   * CASC mode means that we will output messages also in the SZS format.
   */
  static bool cascMode;
private:

  static void runVampireSaturationImpl(ClauseIterator clauses);

  static bool s_haveConjecture;
};

}

#endif // __InputReader__

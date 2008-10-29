/**
 * @file Flattening.hpp
 * Defines class Flattening implementing the flattening inference rule.
 * @since 24/12/2003 Manchester
 */

#ifndef __Flattening__
#define __Flattening__

#include "../Kernel/Formula.hpp"

namespace Kernel {
  class Unit;
}

using namespace Kernel;

namespace Shell {

/**
 * Class implementing flattening-related procedures.
 * @since 23/01/2004 Manchester, changed to include info about positions
 */
class Flattening
{
public:
  static Unit* flatten (Unit*);
private:
  static Formula* flatten (Formula*);
  static FormulaList* flatten (FormulaList*,Connective con);
}; // class Flattening

}

#endif

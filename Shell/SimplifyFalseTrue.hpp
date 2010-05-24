/**
 * @file SimplifyFalseTrue.hpp
 * Defines class SimplifyFalseTrue implementing simplification
 * of formulas containing true or false.
 *
 * @since 11/12/2004 Manchester
 */

#ifndef __SimplifyFalseTrue__
#define __SimplifyFalseTrue__

#include "Kernel/Formula.hpp"

namespace Kernel {
  class Unit;
}

using namespace Kernel;

namespace Shell {

/**
 * Class implementing simplification of formulas containing true or
 * false.
 *
 * @since 11/12/2004 Manchester
 */
class SimplifyFalseTrue
{
public:
  static Unit* simplify(Unit*);
  static Formula* simplify(Formula*);
}; // class SimplifyFalseTrue

}
#endif

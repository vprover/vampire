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
 * @since 25/12/2015 Saint-Petersburg, add FOOL support
 */
class SimplifyFalseTrue
{
public:
  static FormulaUnit* simplify(FormulaUnit*);
  static Formula* simplify(Formula*);
  static TermList simplify(TermList);
}; // class SimplifyFalseTrue

}
#endif

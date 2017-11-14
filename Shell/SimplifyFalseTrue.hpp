
/*
 * File SimplifyFalseTrue.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
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

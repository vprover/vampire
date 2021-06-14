/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
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
  static Formula* simplify(Formula* f){
    auto res = innerSimplify(f);
    res->label(f->getLabel());
    return res;
  }
  static Formula* innerSimplify(Formula*);
  static TermList simplify(TermList);
}; // class SimplifyFalseTrue

}
#endif

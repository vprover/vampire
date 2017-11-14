
/*
 * File Flattening.hpp.
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
 * @file Flattening.hpp
 * Defines class Flattening implementing the flattening inference rule.
 * @since 24/12/2003 Manchester
 */

#ifndef __Flattening__
#define __Flattening__

#include "Forwards.hpp"

#include "Kernel/Formula.hpp"

namespace Shell {

using namespace Kernel;

/**
 * Class implementing flattening-related procedures.
 * @since 23/01/2004 Manchester, changed to include info about positions
 */
class Flattening
{
public:
  static FormulaUnit* flatten (FormulaUnit*);
  static Formula* flatten (Formula*);
  static FormulaList* flatten (FormulaList*,Connective con);
  static Literal* flatten (Literal*);
  static TermList flatten (TermList);

  static Formula* getFlattennedNegation(Formula* f);
private:
}; // class Flattening

}

#endif

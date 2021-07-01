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
 * @file NNF.hpp
 * Defines NNF-related transformations.
 * @since 28/12/2003 Manchester
 * @since 27/06/2007 Flight Frankfurt-Paris, changed to use new data structures
 */

#ifndef __NNF__
#define __NNF__

namespace Kernel {
  class Unit;
};

#include "Kernel/Formula.hpp"

using namespace Kernel;

namespace Shell {

/**
 * Class implementing NNF-related procedures.
 */
class NNF
{
public:
  static FormulaUnit* ennf(FormulaUnit* unit);
  static FormulaUnit* nnf(FormulaUnit* unit);
  static Formula* ennf(Formula*, bool polarity);
private:
  static Literal* ennf(Literal*);
  static TermList ennf(TermList, bool polarity);
  static FormulaList* ennf(FormulaList*, bool polarity);
  static Formula* nnf(Formula*, bool polarity);
  static FormulaList* nnf(FormulaList*, bool polarity);
}; // class NNF

}

#endif

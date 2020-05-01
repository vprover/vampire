
/*
 * File FormulaUnit.hpp.
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
 * @file FormulaUnit.hpp
 * Defines class FormulaUnit for units consisting of formulas.
 *
 * @since 09/05/2007 Manchester
 */

#ifndef __FormulaUnit__
#define __FormulaUnit__

#include "Lib/Allocator.hpp"

#include "Unit.hpp"

using namespace std;
using namespace Lib;

namespace Kernel {

class Formula;

/**
 * Class to represent units of inference deriving formulas.
 * @since 09/05/2007 Manchester
 */
class FormulaUnit
  : public Unit
{
public:
  /** New unit of a given kind */
  FormulaUnit(Formula* f,const Inference& inf)
    : Unit(FORMULA,inf),
      _formula(f), _cachedColor(COLOR_INVALID), _cachedWeight(0)
  {}

  void destroy();
  vstring toString() const;

  unsigned varCnt();

  /** Return the formula of this unit */
  const Formula* formula() const
  { return _formula; }
  /** Return the formula of this unit */
  Formula* formula()
  { return _formula; }

  Color getColor();
  unsigned weight();

  CLASS_NAME(FormulaUnit);
  USE_ALLOCATOR(FormulaUnit);

protected:
  /** Formula of this unit */
  Formula* _formula;

  Color _cachedColor;
  unsigned _cachedWeight;
}; // class FormulaUnit


}
#endif

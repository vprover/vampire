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
  FormulaUnit(Formula* f,Inference* inf,InputType it)
    : Unit(FORMULA,inf,it),
      _formula(f)
  {}

  void destroy();
  string toString() const;

  /** Return the formula of this unit */
  const Formula* formula() const
  { return _formula; }
  /** Return the formula of this unit */
  Formula* formula()
  { return _formula; }


  Color getColor();

  CLASS_NAME("FormulaUnit");
  USE_ALLOCATOR(FormulaUnit);

protected:
  /** Formula of this unit */
  Formula* _formula;
}; // class FormulaUnit


}
#endif

/**
 * @file FormulaUnit.cpp
 * Defines class FormulaUnit for units consisting of formulas.
 *
 * @since 19/05/2007 Manchester
 */

#include "../Lib/Int.hpp"

#include "Formula.hpp"
#include "FormulaUnit.hpp"
#include "Inference.hpp"
#include "SubformulaIterator.hpp"
#include "Term.hpp"

using namespace std;
using namespace Lib;

using namespace Kernel;

/**
 * Destroy the unit by deleting it.
 * @since 19/05/2007 Manchester
 */
void FormulaUnit::destroy()
{
  _inference->destroy();
  delete this;
} // FormulaUnit::destroy


/**
 * Convert the unit to the string representation.
 * @since 20/05/2007 Manchester
 */
string FormulaUnit::toString() const
{
  return Int::toString(_number) + ". " + _formula->toString() +
         ' ' + inferenceAsString();
} // FormulaUnit::toString

/**
 * Return color of the formula
 *
 * We do not store the color of the formula, so it gets
 * computed again each time the function is called.
 */
Color FormulaUnit::getColor()
{
  CALL("FormulaUnit::getColor");

  return this->formula()->getColor();
}

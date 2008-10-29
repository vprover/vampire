/**
 * @file FormulaUnit.cpp
 * Defines class FormulaUnit for units consisting of formulas.
 *
 * @since 19/05/2007 Manchester
 */

#include "../Lib/Int.hpp"

#include "Inference.hpp"
#include "Formula.hpp"
#include "FormulaUnit.hpp"

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


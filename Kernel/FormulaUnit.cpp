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
 * @file FormulaUnit.cpp
 * Defines class FormulaUnit for units consisting of formulas.
 *
 * @since 19/05/2007 Manchester
 */

#include "Lib/Int.hpp"

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
  _inference.destroy(); // decrease counters on parents and release heap allocated things own by _inference
  delete this;
} // FormulaUnit::destroy


/**
 * Convert the unit to the vstring representation.
 * @since 20/05/2007 Manchester
 */
vstring FormulaUnit::toString() const
{
  return Int::toString(_number) + ". " + _formula->toString() +
         ' ' + inferenceAsString();
} // FormulaUnit::toString

unsigned FormulaUnit::varCnt()
{
  CALL("FormulaUnit::varCnt");

  Formula* frm = formula();
  VList* fv = frm->freeVariables();
  VList* bv = frm->boundVariables();

  unsigned res = VList::length(fv) + VList::length(bv);
  VList::destroy(fv);
  VList::destroy(bv);
  return res;
}

/**
 * Return color of the formula
 *
 * We do not store the color of the formula, so it gets
 * computed again each time the function is called.
 */
Color FormulaUnit::getColor()
{
  CALL("FormulaUnit::getColor");
  ASS_ALLOC_TYPE(this, "FormulaUnit");

  if (_cachedColor == COLOR_INVALID) {
    _cachedColor = this->formula()->getColor();
  }
  return _cachedColor;
}

unsigned FormulaUnit::weight()
{
  CALL("FormulaUnit::weight");
  ASS_ALLOC_TYPE(this, "FormulaUnit");

  if (!_cachedWeight) {
    _cachedWeight = this->formula()->weight();
  }
  return _cachedWeight;
}

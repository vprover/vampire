/**
 * @file Unit.cpp
 * Defines class Unit for all kinds of proof units
 *
 * @since 09/05/2007 Manchester
 */

#include "Debug/Tracer.hpp"

#include "Lib/Int.hpp"

#include "BDD.hpp"
#include "Inference.hpp"
#include "Clause.hpp"
#include "Formula.hpp"
#include "FormulaUnit.hpp"

#include "Unit.hpp"

using namespace Kernel;

unsigned Unit::_firstNonPreprocessingNumber = 0;

/**
 * Should be called after the preprocessing and before the start
 * of the saturation algorithm.
 */
void Unit::onPreprocessingEnd()
{
  CALL("Unit::onPreprocessingEnd");
  ASS(!_firstNonPreprocessingNumber);

  _firstNonPreprocessingNumber=_lastNumber;
}

/** New unit of a given kind */
Unit::Unit(Kind kind,Inference* inf,InputType it)
  : _number(++_lastNumber),
    _kind(kind),
    _inputType(it),
    _inheritedColor(COLOR_INVALID),
    _included(0),
    _inference(inf)
{
  switch (inf->rule()) {
  case Inference::INPUT:
  case Inference::NEGATED_CONJECTURE:
    _adam = _number;
    break;
  default:
    {
      Inference::Iterator pars = inf->iterator();
      if (inf->hasNext(pars)) {
	Unit* parent = inf->next(pars);
	_adam = parent->_adam;
      }
      else {
	_adam = -1;
      }
    }
    break;
  }
} // Unit::Unit

Color Unit::getColor()
{
  if(isClause()) {
    return static_cast<Clause*>(this)->color();
  }
  else {
    return static_cast<FormulaUnit*>(this)->getColor();
  }
}

/**
 * Return quantified formula equivalent to the unit.
 */
Formula* Unit::getFormula(BDDNode* prop)
{
  if(isClause()) {
    return Formula::fromClause(static_cast<Clause*>(this), prop);
  }
  else {
    ASS(BDD::instance()->isFalse(prop));
    return Formula::quantify(static_cast<FormulaUnit*>(this)->formula());
  }
}


/**
 * Print the inference as a string (used in printing units in
 * refutations).
 * @since 04/01/2008 Torrevieja
 */
string Unit::inferenceAsString() const
{
  CALL("Unit::inferenceAsString");

  string result = (string)"[" + _inference->name();
  bool first = true;
  Inference::Iterator it = _inference->iterator();
  while (_inference->hasNext(it)) {
    result += first ? ' ' : ',';
    first = false;
    result += Int::toString(_inference->next(it)->number());
  }
  return result + ']';
} // Unit::inferenceAsString()


std::ostream& Kernel::operator<<(ostream& out, const Unit& u)
{
  return out << u.toString();
}

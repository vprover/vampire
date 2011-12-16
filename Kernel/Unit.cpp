/**
 * @file Unit.cpp
 * Defines class Unit for all kinds of proof units
 *
 * @since 09/05/2007 Manchester
 */

#include "Debug/Tracer.hpp"

#include "Lib/Int.hpp"
#include "Lib/List.hpp"

#include "BDD.hpp"
#include "Inference.hpp"
#include "InferenceStore.hpp"
#include "Clause.hpp"
#include "Formula.hpp"
#include "FormulaUnit.hpp"
#include "SubformulaIterator.hpp"

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


/**
 * Return InputType of which should be a formula that has
 * units of types @c t1 and @c t2 as premises.
 */
Unit::InputType Unit::getInputType(InputType t1, InputType t2)
{
  CALL("Unit::getInputType");

  return static_cast<Unit::InputType>(Int::max(t1, t2));
}

/**
 * Return InputType of which should be a formula that has
 * @c units as premises.
 *
 * @c units must be a non-empty list.
 */
Unit::InputType Unit::getInputType(UnitList* units)
{
  CALL("Unit::getInputType");
  ASS(units);

  UnitList::Iterator uit(units);
  ALWAYS(uit.hasNext());
  InputType res = uit.next()->inputType();

  while(uit.hasNext()) {
    res = getInputType(res, uit.next()->inputType());
  }
  return res;
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
 * Add into @c acc numbers of all predicates in the unit.
 * If a predicate occurrs multiple times, it is added once for each occurrence.
 */
void Unit::collectPredicates(Stack<unsigned>& acc)
{
  CALL("Unit::collectPredicates");

  if(isClause()) {
    Clause* cl = static_cast<Clause*>(this);
    unsigned clen = cl->length();
    for(unsigned i=0; i<clen; i++) {
      acc.push((*cl)[i]->functor());
    }
  }
  else {
    Formula* form = static_cast<FormulaUnit*>(this)->formula();
    form->collectPredicates(acc);
  }
}

/**
 * Print the inference as a string (used in printing units in
 * refutations).
 * @since 04/01/2008 Torrevieja
 */
string Unit::inferenceAsString(BDDNode* propPart) const
{
  CALL("Unit::inferenceAsString");

#if 0
  InferenceStore& infS = *InferenceStore::instance();

  Inference::Rule rule;
  UnitSpecIterator parents;
  UnitSpec us = propPart ? UnitSpec(const_cast<Unit*>(this), propPart) : UnitSpec(const_cast<Unit*>(this));
  parents = infS.getParents(us, rule);

  string result = (string)"[" + Inference::ruleName(rule);
  bool first = true;
  while (parents.hasNext()) {
    UnitSpec parent = parents.next();
    result += first ? ' ' : ',';
    first = false;
    result += infS.getUnitIdStr(parent);
  }
  return result + ']';
#else
  string result = (string)"[" + _inference->name();
   bool first = true;
   Inference::Iterator it = _inference->iterator();
   while (_inference->hasNext(it)) {
     result += first ? ' ' : ',';
     first = false;
     result += Int::toString(_inference->next(it)->number());
   }
   return result + ']';
#endif
} // Unit::inferenceAsString()


std::ostream& Kernel::operator<<(ostream& out, const Unit& u)
{
  return out << u.toString();
}

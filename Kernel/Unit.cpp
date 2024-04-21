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
 * @file Unit.cpp
 * Defines class Unit for all kinds of proof units
 *
 * @since 09/05/2007 Manchester
 */

#include "Forwards.hpp"


#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/List.hpp"
#include "Lib/Set.hpp"
#include "Lib/DHMap.hpp"

#include "Inference.hpp"
#include "InferenceStore.hpp"
#include "Clause.hpp"
#include "Formula.hpp"
#include "FormulaUnit.hpp"
#include "SubformulaIterator.hpp"

#include "Unit.hpp"

using namespace std;
using namespace Kernel;

unsigned Unit::_lastNumber = 0;
unsigned Unit::_firstNonPreprocessingNumber = 0;
unsigned Unit::_lastParsingNumber = 0;

/**
 * Should be called after the preprocessing and before the start
 * of the saturation algorithm.
 */
void Unit::onPreprocessingEnd()
{
  ASS(!_firstNonPreprocessingNumber);

  _firstNonPreprocessingNumber=_lastNumber+1;
}

/** New unit of a given kind */
Unit::Unit(Kind kind,const Inference& inf)
  : _number(++_lastNumber),
    _kind(kind),
    _inheritedColor(COLOR_INVALID),
    _inference(inf)
{
} // Unit::Unit

void Unit::incRefCnt()
{
  if(isClause()) {
    static_cast<Clause*>(this)->incRefCnt();
  }
}

void Unit::decRefCnt()
{
  if(isClause()) {
    static_cast<Clause*>(this)->decRefCnt();
  }
}

Clause* Unit::asClause() {
  ASS(isClause());
  return static_cast<Clause*>(this);
}


Color Unit::getColor()
{
  if(isClause()) {
    return static_cast<Clause*>(this)->color();
  }
  else {
    return static_cast<FormulaUnit*>(this)->getColor();
  }
}

unsigned Unit::getWeight()
{
  if(isClause()) {
    return static_cast<Clause*>(this)->weight();
  }
  else {
    return static_cast<FormulaUnit*>(this)->weight();
  }
}

void Unit::destroy()
{
  if(isClause()) {
    static_cast<Clause*>(this)->destroy();
  }
  else {
    static_cast<FormulaUnit*>(this)->destroy();
  }
}

vstring Unit::toString() const
{
  if(isClause()) {
    return static_cast<const Clause*>(this)->toString();
  }
  else {
    return static_cast<const FormulaUnit*>(this)->toString();
  }
}

unsigned Unit::varCnt()
{
  if(isClause()) {
    return static_cast<Clause*>(this)->varCnt();
  }
  else {
    return static_cast<FormulaUnit*>(this)->varCnt();
  }
}


/**
 * Return quantified formula equivalent to the unit.
 *
 * @since 16/01/14, removed BDDNode prop, Giles.
 */
Formula* Unit::getFormula()
{
  if(isClause()) {
    return Formula::fromClause(static_cast<Clause*>(this));//, prop);
  }
  else {
    return Formula::quantify(static_cast<FormulaUnit*>(this)->formula());
  }
}

/**
 * Print the inference as a vstring (used in printing units in
 * refutations).
 * @since 04/01/2008 Torrevieja
 */
vstring Unit::inferenceAsString() const
{
#if 1
  const Inference& inf = inference();

  vstring result = (vstring)"[" + inf.name();
  bool first = true;

  auto it = inf.iterator();
  while (inf.hasNext(it)) {
    Unit* parent = inf.next(it);
    result += first ? ' ' : ',';
    first = false;
    result += Int::toString(parent->number());
  }
  // print Extra
  vstring extra;
  if (env.proofExtra && env.proofExtra->find(this,extra) && extra != "") {
    result += ", " + extra;
  }

  return result + ']';
#else
  vstring result = (vstring)"[" + _inference->name();
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

void Unit::assertValid()
{
  if(isClause()) {
    ASS_ALLOC_TYPE(this,"Clause");
  }
  else {
    ASS_ALLOC_TYPE(this,"FormulaUnit");
  }
}

// TODO this could be more efficient. Although expected cost is log(n) where n is length of proof
bool Unit::derivedFromInput() const
{
  // Depth-first search of derivation - it's likely that we'll hit an input clause as soon
  // as we hit the top
  Stack<Inference*> todo;
  todo.push(&const_cast<Inference&>(_inference));
  while(!todo.isEmpty()){
    Inference* inf = todo.pop();
    if(inf->rule() == InferenceRule::INPUT){
      return true;
    }
    Inference::Iterator it = inf->iterator();
    while(inf->hasNext(it)){ todo.push(&(inf->next(it)->inference())); }
  }

  return false;
}

UnitIterator Unit::getParents() const
{
  // The unit itself stores the inference
  UnitList* res = 0;
  Inference::Iterator iit = _inference.iterator();
  while(_inference.hasNext(iit)) {
    Unit* premUnit = _inference.next(iit);
    UnitList::push(premUnit, res);
  }
  res = UnitList::reverse(res); // we want items in the same order
  return pvi(UnitList::DestructiveIterator(res));
}

std::ostream& Kernel::operator<<(ostream& out, const Unit& u)
{
  return out << u.toString();
}

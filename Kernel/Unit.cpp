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

#include "Debug/Tracer.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/List.hpp"
#include "Lib/Set.hpp"

#include "Inference.hpp"
#include "InferenceStore.hpp"
#include "Clause.hpp"
#include "Formula.hpp"
#include "FormulaUnit.hpp"
#include "SubformulaIterator.hpp"

#include "Unit.hpp"

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
  CALL("Unit::onPreprocessingEnd");
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
  CALL("Unit::incRefCnt");
  if(isClause()) {
    static_cast<Clause*>(this)->incRefCnt();
  }
}

void Unit::decRefCnt()
{
  CALL("Unit::decRefCnt");
  if(isClause()) {
    static_cast<Clause*>(this)->decRefCnt();
  }
}

Clause* Unit::asClause() {
  CALL("Unit::asClause");
  ASS(isClause());
  return static_cast<Clause*>(this);
}


Color Unit::getColor()
{
  CALL("Unit::getColor");

  if(isClause()) {
    return static_cast<Clause*>(this)->color();
  }
  else {
    return static_cast<FormulaUnit*>(this)->getColor();
  }
}

unsigned Unit::getWeight()
{
  CALL("Unit::getWeight");

  if(isClause()) {
    return static_cast<Clause*>(this)->weight();
  }
  else {
    return static_cast<FormulaUnit*>(this)->weight();
  }
}

void Unit::destroy()
{
  CALL("Unit::destroy");

  if(isClause()) {
    static_cast<Clause*>(this)->destroy();
  }
  else {
    static_cast<FormulaUnit*>(this)->destroy();
  }
}

vstring Unit::toString() const
{
  CALL("Unit::toString");

  if(isClause()) {
    return static_cast<const Clause*>(this)->toString();
  }
  else {
    return static_cast<const FormulaUnit*>(this)->toString();
  }
}

unsigned Unit::varCnt()
{
  CALL("Unit::varCnt");

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

void Unit::collectAtoms(Stack<Literal*>& acc)
{
  CALL("Unit::collectAtoms");

  if(isClause()) {
    Clause* cl = static_cast<Clause*>(this);
    Clause::Iterator cit(*cl);
    while(cit.hasNext()) {
      Literal* l = cit.next();
      acc.push(Literal::positiveLiteral(l));
   }
  }
  else {
    Formula* form = static_cast<FormulaUnit*>(this)->formula();
    form->collectAtoms(acc);
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
 * Print the inference as a vstring (used in printing units in
 * refutations).
 * @since 04/01/2008 Torrevieja
 */
vstring Unit::inferenceAsString() const
{
  CALL("Unit::inferenceAsString");

#if 1
  InferenceStore& infS = *InferenceStore::instance();

  InferenceRule rule;
  UnitIterator parents;
  Unit* us = const_cast<Unit*>(this);
  parents = infS.getParents(us, rule);

  vstring result = (vstring)"[" + ruleName(rule);
  bool first = true;
  while (parents.hasNext()) {
    Unit* parent = parents.next();
    result += first ? ' ' : ',';
    first = false;
    result += infS.getUnitIdStr(parent);
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
  CALL("Unit::assertValid");

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
  CALL("Unit::derivedFromInput");

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

typedef List<Inference*> InferenceList;

// TODO this could be more efficient. Although expected cost is log(n) where n is length of proof
bool Unit::derivedFromGoalCheck() const
{
  CALL("Unit::derivedFromGoalCheck");

  // Breadth-first search of derivation - it's likely that we'll hit a goal-related node
  // close to the refutation... unless it doesn't exist of course
  InferenceList* todo = InferenceList::empty();
  Set<Inference*> seen;
  InferenceList::push(&const_cast<Inference&>(_inference),todo);
  while(!InferenceList::isEmpty(todo)){
    Inference* inf = InferenceList::pop(todo);
    if(inf->derivedFromGoal()) {
      return true;
    }
    Inference::Iterator it = inf->iterator();
    while(inf->hasNext(it)){ 
      Inference* ninf = &inf->next(it)->inference();
      if(!seen.contains(ninf)){
       InferenceList::push(ninf,todo); 
       seen.insert(ninf);
      }
    }
  }

  return false;
}

std::ostream& Kernel::operator<<(ostream& out, const Unit& u)
{
  return out << u.toString();
}

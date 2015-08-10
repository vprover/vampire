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

  _firstNonPreprocessingNumber=_lastNumber+1;
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

unsigned Unit::getPriority() const
{
  CALL("Unit::getPriority");

  if(!env.clausePriorities) return 1;

  // Put these at the end of the priority list
  if(
    _inference->rule() == Inference::THEORY ||
    _inference->rule() == Inference::EQUALITY_PROXY_AXIOM1
  ){
    return env.maxClausePriority;
  }
  // Current cases where there is no input clause ancestor
  // This is probably okay as this rule is from a weird experimental option
  if(
     _inference->rule() == Inference::SKOLEM_PREDICATE_INTRODUCTION 
    ){
    // This is the same as depth 1 in sine selection
    return 2;
  }

  unsigned priority;
  if(env.clausePriorities->find(this,priority)){
    return priority;
  }

  // This means we're in LTB mode without SineSelection
  // All learned formauls get 1 so we give non-learned formulas 2
  // Goal gets 1
  if(_inference->rule() == Inference::INPUT){ return 2; }
  if(_inference->rule() == Inference::NEGATED_CONJECTURE){ return 2; }

  // If we get to here it means that the component did not have an orig
  if(_inference->rule() == Inference::SAT_SPLITTING_COMPONENT){ return 2;} 

  //cout << "getPriority for " << this->toString() << endl;

    unsigned count=0;
    unsigned total=0;
    ASS(_inference);
    Unit* t = const_cast<Unit*>(this);
    UnitIterator uit = InferenceStore::instance()->getParents(t);
    while(uit.hasNext()) {
      Unit* us = uit.next();
      unsigned up = us->getPriority();
      count++;
      total+=up;
    }
    //if(count==0){ cout << "count is zero for " << toString() << endl; }
    ASS_G(count,0);

    // If count==0 we are only here in release mode
    if(count==0){ return 2; }

    // we take the average using integer division
    priority = total/count;
    ASS_G(priority,0);

    // I don't think this can happen but a release mode check
    if(priority==0){ priority=1; }

    // record it
    env.clausePriorities->insert(this,priority);

    //cout << "priority is " << priority << endl;

    return priority;
}


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
  if(isClause()) {
    return static_cast<Clause*>(this)->color();
  }
  else {
    return static_cast<FormulaUnit*>(this)->getColor();
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
Formula* Unit::getFormula()//BDDNode* prop)
{
  if(isClause()) {
    return Formula::fromClause(static_cast<Clause*>(this));//, prop);
  }
  else {
    //ASS(BDD::instance()->isFalse(prop));
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

  Inference::Rule rule;
  UnitIterator parents;
  Unit* us = const_cast<Unit*>(this);
  parents = infS.getParents(us, rule);

  vstring result = (vstring)"[" + Inference::ruleName(rule);
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

std::ostream& Kernel::operator<<(ostream& out, const Unit& u)
{
  return out << u.toString();
}

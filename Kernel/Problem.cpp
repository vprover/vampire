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
 * @file Kernel/Problem.cpp
 * Implements class Problem.
 */

#include "Lib/Environment.hpp"
#include "Lib/List.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/ScopedLet.hpp"
#include "Debug/TimeProfiling.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Shell/Property.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/FunctionDefinitionHandler.hpp"

#include "Clause.hpp"
#include "Term.hpp"

#include "Problem.hpp"

#undef LOGGING
#define LOGGING 0

using namespace Lib;
using namespace Kernel;

/**
 * Create a problem object.
 *
 * The new object takes ownership of the list @c units.
 */
Problem::Problem(UnitList* units)
: _units(0), _fnDefHandler(new FunctionDefinitionHandler()), _smtlibLogic(SMTLIBLogic::SMT_UNDEFINED), _property(0)
{
  initValues();

  addUnits(units);
}

/**
 * Create a problem object.
 *
 * If @c copy is false, the new object takes ownership of the
 * clauses in the iterator.
 */
Problem::Problem(ClauseIterator clauses, bool copy)
: _units(0), _fnDefHandler(new FunctionDefinitionHandler()), _property(0)
{
  initValues();

  UnitList* units = 0;
  while(clauses.hasNext()) {
    Clause* cl = clauses.next();
    if(copy) {
      cl = Clause::fromClause(cl);
    }
    UnitList::push(cl, units);
  }
  addUnits(units);

}

Problem::~Problem()
{
  // Don't delete the property as it is owned by Environment
}

/**
 * Initialize values of information in the problem
 *
 * This function we have to share the initialisation code among different
 * constructors.
 */
void Problem::initValues()
{
  _hadIncompleteTransformation = false;
  _mayHaveEquality = true;
  _mayHaveFormulas = true;
  _mayHaveFunctionDefinitions = true;
  _mayHaveInequalityResolvableWithDeletion = true;
  _mayHaveXEqualsY = true;
  _propertyValid = false;
}

/**
 * Add units into the problem. If the property object is valid, update it
 * so that it stays valid, otherwise invalidate the stored knowledge of the
 * problem.
 */
void Problem::addUnits(UnitList* newUnits)
{
  UnitList::Iterator uit(newUnits);
  while(uit.hasNext()) {
    Unit* u = uit.next();
    if(u->isClause()) {
      static_cast<Clause*>(u)->incRefCnt();
    }
  }
  _units = UnitList::concat(newUnits, _units);
  if(_propertyValid) {
    TIME_TRACE(TimeTrace::PROPERTY_EVALUATION);
    _property->add(newUnits);
    readDetailsFromProperty();
  }
  else {
    invalidateEverything();
  }
}

/**
 * Iterator going through the clauses in the problem.
 * When this function is called, problem can no longer
 * contain formulas.
 */
ClauseIterator Problem::clauseIterator() const
{
  //we first call mayHaveFormulas(). if this returns false, we know there are
  //no formulas. otherwise we call hasFormulas() which may cause rescanning
  //the problem property
  ASS(!mayHaveFormulas() || !hasFormulas());
  return pvi( iterTraits(UnitList::Iterator(units())).map([](Unit* u) { return (Clause*)u; }) );
}

/**
 * Creates a copy of this problem object.
 *
 * We do not use the copy constructor for this purpose, because copying
 * of problems is a rare operation and we want to avoid unnoticed bugs
 * coming from passing the Problem object as an argument by value rather
 * than by reference.
 */
Problem* Problem::copy(bool copyClauses)
{
  Problem* res = new Problem();
  copyInto(*res, copyClauses);
  return res;
}

/**
 * Creates a copy of this problem object.
 *
 * We do not use the copy constructor for this purpose, because copying
 * of problems is a rare operation and we want to avoid unnoticed bugs
 * coming from passing the Problem object as an argument by value rather
 * than by reference.
 */
void Problem::copyInto(Problem& tgt, bool copyClauses)
{
  tgt.setSMTLIBLogic(getSMTLIBLogic());

  if(copyClauses) {
    UnitList* newUnits = 0;
    UnitList::Iterator uit(units());
    while(uit.hasNext()) {
      Unit* u = uit.next();
      if(!u->isClause()) {
	UnitList::push(u, newUnits);
	continue;
      }
      Clause* cl = static_cast<Clause*>(u);
      Clause* newCl = Clause::fromClause(cl);
      UnitList::push(newCl, newUnits);
    }
    tgt.addUnits(UnitList::reverse(newUnits));
  }else {
    tgt.addUnits(UnitList::copy(units()));
  }
  if(hadIncompleteTransformation()) {
    tgt.reportIncompleteTransformation();
  }
  if(isPropertyUpToDate()) {
    //if we have an up-to-date property, we just copy it into the
    //copied object so we save ourselves scanning for the property
    //in the child
    tgt._propertyValid = true;
    //warning: both objects contain a pointer to the same property.
    //after copying, the property should be treated as strictly read
    //only.
    tgt._property = _property;
    tgt.readDetailsFromProperty();
  }

  //TODO copy the deleted maps
}

/**
 * Register a trivial predicate that has been removed from the problem
 *
 * Trivial predicates are the predicates whose all occurrences
 * can be assigned either true or false.
 *
 * This information may be used during model output
 */
void Problem::addTrivialPredicate(unsigned pred, bool assignment)
{
  ALWAYS(_trivialPredicates.insert(pred, assignment));
}

/**
 * Register a function that has been eliminated from the problem
 *
 * This information may be used during model output
 */
void Problem::addEliminatedFunction(unsigned func, Literal* definition)
{
  ASS(definition->isEquality());

  _deletedFunctions.insert(func,definition);
}

/**
 * Register a predicate that has been eliminated from the problem
 *
 * This information may be used during model output
 */
void Problem::addEliminatedPredicate(unsigned pred, Unit* definition)
{
  _deletedPredicates.insert(pred,definition);
}

/**
 * Register a predicate that has been partially eliminated i.e. <=> replaced by => 
 *
 * This information may be used during model output
 */
void Problem::addPartiallyEliminatedPredicate(unsigned pred, Unit* definition)
{
  _partiallyDeletedPredicates.insert(pred,definition);
}

/**
 * Recalculate the property from the current set of formulas
 */
void Problem::refreshProperty() const
{
  TIME_TRACE(TimeTrace::PROPERTY_EVALUATION);
  ScopedLet<Statistics::ExecutionPhase> phaseLet(env.statistics->phase, Statistics::PROPERTY_SCANNING);

  auto oldProp = _property;
  _propertyValid = true;
  _property = Property::scan(_units);
  if(oldProp) {
    delete oldProp;
  }
  ASS(_property);
  _property->setSMTLIBLogic(getSMTLIBLogic());
  readDetailsFromProperty();
}

/**
 * Read the locally stored information from the Property object
 */
void Problem::readDetailsFromProperty() const
{
  _hasFormulas = _property->hasFormulas();
  _hasEquality = _property->equalityAtoms()!=0;
  _hasInterpretedOperations = _property->hasInterpretedOperations();
  _hasNumerals = _property->hasNumerals();
  _hasFOOL = _property->hasFOOL();
  _hasCombs = _property->hasCombs();
  _hasApp = _property->hasApp();
  _hasAppliedVar = _property->hasAppliedVar();
  _hasLogicalProxy = _property->hasLogicalProxy();
  _hasPolymorphicSym = _property->hasPolymorphicSym();
  _quantifiesOverPolymorphicVar = _property->quantifiesOverPolymorphicVar();
  _hasBoolVar = _property->hasBoolVar();
  _higherOrder = _property->higherOrder();
  _hasNonDefaultSorts = _property->hasNonDefaultSorts();

  _mayHaveFormulas = _hasFormulas.value();
  _mayHaveEquality = _hasEquality.value();
  _mayHaveFunctionDefinitions = _property->hasProp(Property::PR_HAS_FUNCTION_DEFINITIONS);
  _mayHaveInequalityResolvableWithDeletion = _property->hasProp(Property::PR_HAS_INEQUALITY_RESOLVABLE_WITH_DELETION);
  _mayHaveXEqualsY = _property->hasProp(Property::PR_HAS_X_EQUALS_Y);
}

/**
 * Invalidate all the information stored about the problem
 */
void Problem::invalidateEverything()
{
  invalidateProperty();
  _hasFormulas = MaybeBool::Unknown;
  _hasEquality = MaybeBool::Unknown;
  _hasInterpretedOperations = MaybeBool::Unknown;
  _hasNumerals = MaybeBool::Unknown;
  _hasFOOL = MaybeBool::Unknown;
  _hasCombs = MaybeBool::Unknown;
  _hasApp = MaybeBool::Unknown;
  _hasAppliedVar = MaybeBool::Unknown;

  _mayHaveFormulas = true;
  _mayHaveEquality = true;
  _mayHaveFunctionDefinitions = true;
  _mayHaveInequalityResolvableWithDeletion = true;
  _mayHaveXEqualsY = true;
}

/**
 * Invalidate the information about problem that could have been
 * violated by removing some formulas or their parts
 */
void Problem::invalidateByRemoval()
{
  invalidateProperty();
  _hasFormulas.mightBecameFalse();
  _hasEquality.mightBecameFalse();
  _hasInterpretedOperations.mightBecameFalse();
  _hasNumerals.mightBecameFalse();
  _hasFOOL.mightBecameFalse();
  _hasCombs.mightBecameFalse();
  _hasAppliedVar.mightBecameFalse();
  _hasLogicalProxy.mightBecameFalse();
  _hasPolymorphicSym.mightBecameFalse();
  _quantifiesOverPolymorphicVar.mightBecameFalse();
  _hasBoolVar.mightBecameFalse();
}

/**
 * Return property corresponding to the current state of the problem
 */
Property* Problem::getProperty() const
{
  if(!_propertyValid) {
    refreshProperty();
  }
  ASS(_property);

  return _property;
}


bool Problem::hasFormulas() const
{
  if(!mayHaveFormulas()) { return false; }
  if(!_hasFormulas.known()) { refreshProperty(); }  
  ASS(_hasFormulas.known());
  return _hasFormulas.value();
}

bool Problem::hasEquality() const
{
  if(!mayHaveEquality()) { return false; }
  if(!_hasEquality.known()) { refreshProperty(); }
  return _hasEquality.value();
}

bool Problem::hasInterpretedOperations() const
{
  if(!_hasInterpretedOperations.known()) { refreshProperty(); }
  return _hasInterpretedOperations.value();
}

bool Problem::hasNumerals() const
{
  if(!_hasNumerals.known()) { refreshProperty(); }
  return _hasNumerals.value();
}

bool Problem::hasFOOL() const
{
  if(!_hasFOOL.known()) { refreshProperty(); }
  return _hasFOOL.value();
}

bool Problem::hasCombs() const
{
  if(!_hasCombs.known()) { refreshProperty(); }
  return _hasCombs.value();
}


bool Problem::hasApp() const
{
  if(!_hasApp.known()) { refreshProperty(); }
  return _hasApp.value();
}

bool Problem::hasAppliedVar() const
{
  if(!_hasAppliedVar.known()) { refreshProperty(); }
  return _hasAppliedVar.value();
}

bool Problem::hasBoolVar() const
{
  if(!_hasBoolVar.known()) { refreshProperty(); }
  return _hasBoolVar.value();
}


bool Problem::hasLogicalProxy() const
{
  if(!_hasLogicalProxy.known()) { refreshProperty(); }
  return _hasLogicalProxy.value();
}

bool Problem::hasPolymorphicSym() const
{
  if(!_hasPolymorphicSym.known()) { refreshProperty(); }
  return _hasPolymorphicSym.value();
}

bool Problem::quantifiesOverPolymorphicVar() const
{
  if(!_quantifiesOverPolymorphicVar.known()) { refreshProperty(); }
  return _quantifiesOverPolymorphicVar.value();
}

bool Problem::isHigherOrder() const
{
  if(!_higherOrder.known()) { refreshProperty(); }
  return _higherOrder.value();
}

bool Problem::hasNonDefaultSorts() const
{
  if(!_hasNonDefaultSorts.known()) { refreshProperty(); }
  return _hasNonDefaultSorts.value();
}

#if VDEBUG
///////////////////////
// debugging
//
void Problem::assertValid()
{
  UnitList::Iterator uit(units());
  while(uit.hasNext()) {
    Unit* u = uit.next();
    ASSERT_VALID(*u);
  }
}
#endif

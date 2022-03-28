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
#include "Lib/TimeCounter.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Shell/Property.hpp"
#include "Shell/Statistics.hpp"

#include "Clause.hpp"
#include "Term.hpp"

#include "Problem.hpp"

#undef LOGGING
#define LOGGING 0

using namespace Kernel;

/**
 * Create a problem object.
 *
 * The new object takes ownership of the list @c units.
 */
Problem::Problem(UnitList* units)
: _units(0), _smtlibLogic(SMTLIBLogic::SMT_UNDEFINED) 
{
  CALL("Problem::Problem(UnitList*)");

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
: _units(0)
{
  CALL("Problem::Problem(ClauseIterator,bool)");

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
  CALL("Problem::~Problem");
  //TODO: decrease reference counter of clauses (but make sure there's no segfault...)

  UnitList::destroy(_units);
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
  CALL("Problem::initValues");

  _hadIncompleteTransformation = false;
  _mayHaveEquality = true;
  _mayHaveFormulas = true;
  _mayHaveFunctionDefinitions = true;
  _mayHaveInequalityResolvableWithDeletion = true;
  _mayHaveXEqualsY = true;
  _propertyValid = false;
  _property = env.property;
}

/**
 * Add units into the problem. If the property object is valid, update it
 * so that it stays valid, otherwise invalidate the stored knowledge of the
 * problem.
 */
void Problem::addUnits(UnitList* newUnits)
{
  CALL("Problem::addUnits");

  UnitList::Iterator uit(newUnits);
  while(uit.hasNext()) {
    Unit* u = uit.next();
    if(u->isClause()) {
      static_cast<Clause*>(u)->incRefCnt();
    }
  }
  _units = UnitList::concat(newUnits, _units);
  if(_propertyValid) {
    TimeCounter tc(TC_PROPERTY_EVALUATION);
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
  CALL("Problem::clauseIterator");

  //we first call mayHaveFormulas(). if this returns false, we know there are
  //no formulas. otherwise we call hasFormulas() which may cause rescanning
  //the problem property
  ASS(!mayHaveFormulas() || !hasFormulas());
  return pvi( getStaticCastIterator<Clause*>(UnitList::Iterator(units())) );
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
  CALL("Problem::copy/1");

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
  CALL("Problem::copy/2");

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
  CALL("Problem::addTrivialPredicate");

  ALWAYS(_trivialPredicates.insert(pred, assignment));
}

void Problem::addBDDVarMeaning(unsigned var, BDDMeaningSpec spec) {
  CALL("Problem::addBDDVarMeaning");
  ASS(!spec.first || spec.first->ground());

  ALWAYS(_bddVarSpecs.insert(var, spec));
}

/**
 * Register a function that has been eliminated from the problem
 *
 * This information may be used during model output
 */
void Problem::addEliminatedFunction(unsigned func, Literal* definition)
{
  CALL("Problem::addEliminatedFunction");
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
  CALL("Problem::addEliminatedPredicate");

  _deletedPredicates.insert(pred,definition);
}

/**
 * Register a predicate that has been partially eliminated i.e. <=> replaced by => 
 *
 * This information may be used during model output
 */
void Problem::addPartiallyEliminatedPredicate(unsigned pred, Unit* definition)
{
  CALL("Problem::addPurePredicateDefinition");

  _partiallyDeletedPredicates.insert(pred,definition);
}

/**
 * Recalculate the property from the current set of formulas
 */
void Problem::refreshProperty() const
{
  CALL("Problem::refreshProperty");

  TimeCounter tc(TC_PROPERTY_EVALUATION);
  ScopedLet<Statistics::ExecutionPhase> phaseLet(env.statistics->phase, Statistics::PROPERTY_SCANNING);

  if(_property) {
    delete _property;
  }
  _propertyValid = true;
  _property = Property::scan(_units);
  env.property = _property;
  ASS(_property);
  _property->setSMTLIBLogic(getSMTLIBLogic());
  readDetailsFromProperty();
}

/**
 * Read the locally stored information from the Property object
 */
void Problem::readDetailsFromProperty() const
{
  CALL("Problem::readDetailsFromProperty");

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
  CALL("Problem::invalidateEverything");

  invalidateProperty();
  _hasFormulas = MaybeBool::UNKNOWN;
  _hasEquality = MaybeBool::UNKNOWN;
  _hasInterpretedOperations = MaybeBool::UNKNOWN;
  _hasNumerals = MaybeBool::UNKNOWN;
  _hasFOOL = MaybeBool::UNKNOWN;
  _hasCombs = MaybeBool::UNKNOWN;
  _hasApp = MaybeBool::UNKNOWN;
  _hasAppliedVar = MaybeBool::UNKNOWN;

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
  CALL("Problem::invalidateByRemoval");

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
  CALL("Problem::getProperty");

  if(!_propertyValid) {
    refreshProperty();
  }
  ASS(_property);

  return _property;
}


bool Problem::hasFormulas() const
{
  CALL("Problem::hasFormulas");

  if(!mayHaveFormulas()) { return false; }
  if(!_hasFormulas.known()) { refreshProperty(); }  
  ASS(_hasFormulas.known());
  return _hasFormulas.value();
}

bool Problem::hasEquality() const
{
  CALL("Problem::hasEquality");

  if(!mayHaveEquality()) { return false; }
  if(!_hasEquality.known()) { refreshProperty(); }
  return _hasEquality.value();
}

bool Problem::hasInterpretedOperations() const
{
  CALL("Problem::hasInterpretedOperations");

  if(!_hasInterpretedOperations.known()) { refreshProperty(); }
  return _hasInterpretedOperations.value();
}

bool Problem::hasNumerals() const
{
  CALL("Problem::hasNumerals");

  if(!_hasNumerals.known()) { refreshProperty(); }
  return _hasNumerals.value();
}

bool Problem::hasFOOL() const
{
  CALL("Problem::hasFOOL");

  if(!_hasFOOL.known()) { refreshProperty(); }
  return _hasFOOL.value();
}

bool Problem::hasCombs() const
{
  CALL("Problem::hasCombs");

  if(!_hasCombs.known()) { refreshProperty(); }
  return _hasCombs.value();
}


bool Problem::hasApp() const
{
  CALL("Problem::hasApp");

  if(!_hasApp.known()) { refreshProperty(); }
  return _hasApp.value();
}

bool Problem::hasAppliedVar() const
{
  CALL("Problem::hasAppliedVar");

  if(!_hasAppliedVar.known()) { refreshProperty(); }
  return _hasAppliedVar.value();
}

bool Problem::hasBoolVar() const
{
  CALL("Problem::hasBoolVar");

  if(!_hasBoolVar.known()) { refreshProperty(); }
  return _hasBoolVar.value();
}


bool Problem::hasLogicalProxy() const
{
  CALL("Problem::hasLogicalProxy");

  if(!_hasLogicalProxy.known()) { refreshProperty(); }
  return _hasLogicalProxy.value();
}

bool Problem::hasPolymorphicSym() const
{
  CALL("Problem::hasPolymorphicSym");

  if(!_hasPolymorphicSym.known()) { refreshProperty(); }
  return _hasPolymorphicSym.value();
}

bool Problem::quantifiesOverPolymorphicVar() const
{
  CALL(" Problem::quantifiesOverPolymorphicVar");

  if(!_quantifiesOverPolymorphicVar.known()) { refreshProperty(); }
  return _quantifiesOverPolymorphicVar.value();
}

bool Problem::higherOrder() const
{
  CALL("Problem::hasPolymorphicSym");

  if(!_higherOrder.known()) { refreshProperty(); }
  return _higherOrder.value();
}


///////////////////////
// utility functions
//

/**
 * Put predicate numbers present in the problem into @c acc
 *
 * The numbers added to acc are not unique.
 *
 */
void Problem::collectPredicates(Stack<unsigned>& acc) const
{
  CALL("Problem::collectPredicates");

  UnitList::Iterator uit(units());
  while(uit.hasNext()) {
    Unit* u = uit.next();
    u->collectPredicates(acc);
  }
}

#if VDEBUG
///////////////////////
// debugging
//
void Problem::assertValid()
{
  CALL("Problem::assertValid");

  UnitList::Iterator uit(units());
  while(uit.hasNext()) {
    Unit* u = uit.next();
    ASSERT_VALID(*u);
  }
}
#endif

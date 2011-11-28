/**
 * @file Problem.cpp
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

namespace Kernel
{

/**
 * Create a problem object.
 *
 * The new object takes ownership of the list @c units.
 */
Problem::Problem(UnitList* units)
: _units(units)
{
  CALL("Problem::Problem(UnitList*)");

  initValues();
}

/**
 * Create a problem object.
 *
 * If @c copy is false, the new object takes ownership of the
 * clauses in the iterator.
 */
Problem::Problem(ClauseIterator clauses, bool copy)
{
  CALL("Problem::Problem(ClauseIterator,bool)");

  UnitList* units = 0;
  while(clauses.hasNext()) {
    Clause* cl = clauses.next();
    if(copy) {
      cl = Clause::fromClause(cl);
    }
    UnitList::push(cl, units);
  }
  _units = units;

  initValues();
}

Problem::~Problem()
{
  CALL("Problem::~Problem");

  if(_property) { delete _property; }
}

/**
 * Initialize values of information in the problem
 *
 * This function we have to share the initialization code among different
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
  _property = 0;
}

/**
 * Add units into the problem. If the property object is valid, update it
 * so that it stays valid, otherwise invalidate the stored knowledge of the
 * problem.
 */
void Problem::addUnits(UnitList* newUnits)
{
  CALL("Problem::addUnits");

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

  UnitList* newUnits;
  if(copyClauses) {
    newUnits = 0;
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
    tgt.addUnits(newUnits->reverse());
  }else {
    tgt.addUnits(units()->copy());
  }
  if(hadIncompleteTransformation()) {
    tgt.reportIncompleteTransformation();
  }
  if(isPropertyUpToDate()) {
    //if we have an up-to-date property, we just copy it into the
    //copyed opbect so we save ourselves scanning for the property
    //in the child
    tgt._propertyValid = true;
    tgt._property = new Property(*_property);
    tgt.readDetailsFromProperty();
  }
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

/**
 * Register a function that has been eliminated from the problem
 *
 * This information may be used during model output
 */
void Problem::addEliminatedFunction(unsigned func, Literal* definition)
{
  CALL("Problem::addEliminatedFunction");
  ASS(definition->isEquality());

  //TODO:to be implemented and handled in model retrieval
}

/**
 * Register a predicate that has been eliminated from the problem
 *
 * This information may be used during model output
 */
void Problem::addEliminatedPredicate(unsigned pred, Unit* definition)
{
  CALL("Problem::addEliminatedPredicate");

  //TODO:to be implemented and handled in model retrieval
}

/**
 * Recalculate the property from the current set of formulas
 */
void Problem::refreshProperty() const
{
  CALL("Problem::refreshProperty");

  LOG("prb_prop_refresh","property scanned");

  TimeCounter tc(TC_PROPERTY_EVALUATION);
  ScopedLet<Statistics::ExecutionPhase> phaseLet(env.statistics->phase, Statistics::PROPERTY_SCANNING);

  if(_property) {
    delete _property;
  }
  _propertyValid = true;
  _property = Property::scan(_units);

  readDetailsFromProperty();
}

/**
 * Read the localy stored information from the Property object
 */
void Problem::readDetailsFromProperty() const
{
  CALL("Problem::readDetailsFromProperty");

  _hasFormulas = _property->hasFormulas();
  _hasEquality = _property->equalityAtoms()!=0;
  _hasInterpretedOperations = _property->hasInterpretedOperations();
  _hasSpecialTermsOrLets = _property->hasSpecialTermsOrLets();
  _hasFormulaItes = _property->hasFormulaItes();

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
  _hasSpecialTermsOrLets = MaybeBool::UNKNOWN;
  _hasFormulaItes = MaybeBool::UNKNOWN;

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
  _hasSpecialTermsOrLets.mightBecameFalse();
  _hasFormulaItes.mightBecameFalse();
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
  return _hasEquality.value();
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

bool Problem::hasSpecialTermsOrLets() const
{
  CALL("Problem::hasSpecialTermsOrLets");

  if(!_hasSpecialTermsOrLets.known()) { refreshProperty(); }
  return _hasSpecialTermsOrLets.value();
}

bool Problem::hasFormulaItes() const
{
  CALL("Problem::hasFormulaItes");

  if(!_hasFormulaItes.known()) { refreshProperty(); }
  return _hasFormulaItes.value();
}


}

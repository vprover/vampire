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

using namespace Kernel;

/**
 * Create a problem object.
 *
 * The new object takes ownership of the list @c units.
 */
Problem::Problem(UnitList* units)
: _units(0), _fnDefHandler(new FunctionDefinitionHandler()), _smtlibLogic(SMTLIBLogic::UNDEFINED), _property(0)
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

void Problem::FunDef::outputDefinition(std::ostream& out)
{
  out << "for all inputs,\n    define " << _head->toString() << " := " << _body->toString() << std::endl;
}

void Problem::PredDef::outputDefinition(std::ostream& out)
{
  out << "for all inputs,\n    define " << _head->toString() << " := " << _body->toString() << std::endl;
}

void Problem::GlobalFlip::outputDefinition(std::ostream& out)
{
  out << "globally flip the polarity of every occurrence of predicate \""
    << env.signature->predicateName(_pred) << "\"" << std::endl;
}

void Problem::CondFlip::outputDefinition(std::ostream& out)
{
  out << "for all groundings,";
  if (_fixedPoint) {
    out << " until fixed point,";
  }
  out << "\n    whenever " << _cond->toString() << " is "
    << (_neg ? "false" : "true") <<  ", set " << _val->toString() << " to true" << std::endl;
}

/**
 * Register a trivial predicate that has been removed from the problem
 *
 * Trivial predicates are the predicates whose all occurrences
 * can be assigned either true or false.
 *
 * This information may be used during model output.
 */
void Problem::addTrivialPredicate(unsigned pred, bool assignment)
{
  // create linear literal (~)pred(X0,X1,...X_arity)
  TermStack args;
  for (unsigned v = 0; v < env.signature->getPredicate(pred)->arity(); v++) {
    args.push(TermList(v,false));
  }
  Literal* l = Literal::create(pred, args.size(), true, args.begin());

  auto res = new PredDef(l,new Formula(assignment));

  interferences.push(res);
}

/**
 * Register a predicate that has been partially eliminated i.e. <=> replaced by =>
 *
 * This information may be used during model output
 */
void Problem::addPartiallyEliminatedPredicate(unsigned pred, Formula* remainingImplication)
{
  Formula* f;
  bool isQuantified=remainingImplication->connective()==FORALL;
  if(isQuantified) {
    f=remainingImplication->qarg();
  } else {
    f=remainingImplication;
  }
  ASS_EQ(f->connective(),IMP)

  Formula* cond;
  Literal* new_atom_val;
  bool neg = false;
  if (f->left()->connective()==LITERAL && f->left()->literal()->functor()==pred) {
    new_atom_val =f->left()->literal();
    cond = f->right();
  } else {
    ASS(f->right()->connective()==LITERAL && f->right()->literal()->functor()==pred)
    new_atom_val = Literal::complementaryLiteral(f->right()->literal());
    if (f->left()->connective()==NOT) {
      cond = f->left()->uarg();
    } else {
      cond = f->left();
      neg = true;
    }
  }

  auto res = new CondFlip(cond,neg,new_atom_val);
  interferences.push(res);
}

/**
 * Register a predicate that has been eliminated from the problem
 *
 * This information may be used during model output
 */
void Problem::addEliminatedPredicate(unsigned pred, Formula* def)
{
  Formula* f;
  bool isQuantified=def->connective()==FORALL;
  if(isQuantified) {
    f=def->qarg();
  } else {
    f=def;
  }
  ASS_EQ(f->connective(),IFF)

  Formula* lhs;
  Formula* rhs;
  if(f->left()->connective()==LITERAL && f->left()->literal()->functor()==pred) {
    lhs=f->left();
    rhs=f->right();
  } else {
    lhs = f->right();
    rhs = f->left();
  }
  ASS(lhs->connective()==LITERAL && lhs->literal()->functor()==pred)

  auto res = new PredDef(lhs->literal(),rhs);
  interferences.push(res);
}

/**
 * Register a predicate with flipped polarity.
 */
void Problem::addFlippedPredicate(unsigned pred)
{
  interferences.push(new GlobalFlip(pred));
}

/**
 * Register a function that has been eliminated from the problem
 *
 * This information may be used during model output
 */
void Problem::addEliminatedFunction(unsigned func, Literal* definition) {
  ASS(definition->isEquality());
  TermList* args = definition->args();
  ASS(!args->isVar())
  Term* l = args->term();
  args = args->next();
  ASS(!args->isVar())
  Term* r = args->term();

  Interference* res;
  if (l->functor() == func) {
    res = new FunDef(l,r);
  } else {
    ASS(r->functor() == func)
    res = new FunDef(r,l);
  }

  interferences.push(res);
}

void Problem::addEliminatedBlockedClause(Clause* cl, unsigned blockedLiteralIndex) {
  Literal* bll = (*cl)[blockedLiteralIndex];
  Formula* cond= Formula::fromClause(cl,/* closed= */false);

  bool needsFixpoint = false;
  for (unsigned i = 0; i < cl->size(); i++) {
    Literal* other = (*cl)[i];
    if (other->functor() == bll->functor() && other->polarity() != bll->polarity()) {
      needsFixpoint = true;
      break;
    }
  }

  auto res = new CondFlip(cond,true,bll,needsFixpoint);

  interferences.push(res);
}

/**
 * Recalculate the property from the current set of formulas
 */
void Problem::refreshProperty() const
{
  TIME_TRACE(TimeTrace::PROPERTY_EVALUATION);
  ScopedLet<ExecutionPhase> phaseLet(env.statistics->phase, ExecutionPhase::PROPERTY_SCANNING);

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
  _hasAlascaArithmetic = _property->hasNumerals()
    || forAnyNumTraits([&](auto n) { return 
           _property->hasInterpretedOperation(n.addI)
        || _property->hasInterpretedOperation(n.mulI)
        || _property->hasInterpretedOperation(n.floorI);
        });
  _hasFOOL = _property->hasFOOL();
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
  _hasAlascaArithmetic = MaybeBool::Unknown;
  _hasFOOL = MaybeBool::Unknown;
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
  _hasAlascaArithmetic.mightBecameFalse();
  _hasFOOL.mightBecameFalse();
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

bool Problem::hasAlascaArithmetic() const
{
  if(!_hasAlascaArithmetic.known()) { refreshProperty(); }
  return _hasAlascaArithmetic.value();
}

bool Problem::hasAlascaMixedArithmetic() const
{
  return hasAlascaArithmetic() 
    && forAnyNumTraits([&](auto n) {
        return getProperty()->hasInterpretedOperation(n.floorI);
    });
}

bool Problem::hasFOOL() const
{
  if(!_hasFOOL.known()) { refreshProperty(); }
  return _hasFOOL.value();
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

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
 * @file Kernel/Problem.hpp
 * Defines class Problem.
 */

#ifndef __Kernel_Problem__
#define __Kernel_Problem__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/MaybeBool.hpp"

#include "Shell/SMTLIBLogic.hpp"

namespace Kernel {

using namespace Lib;
using namespace Shell;

/**
 * Class representing a TPTP problem to be solved
 *
 * The main benefit of this class is that it can carry information about
 * all preprocessing performed on a problem. This can be necessary for
 * outputting models.
 *
 * Functions has... answer with certainty whether the problem (in its current state)
 * has certain property.
 *
 * Functions mayHave... provide answer that may err on the positive side --
 * for example mayHaveEquality() may return true for a problem that no longer
 * has equality because it was removed somewhere during preprocessing.
 * These functions are present so that we do not need to keep track of
 * every step performed by the preprocessor, and at the same time we do not
 * need to reevaluate the Property object with each call to such function.
 */
class Problem {
private:
  Problem(const Problem&); //private and undefined copy constructor
  Problem& operator=(const Problem&); //private and undefined assignment operator
public:

  CLASS_NAME(Problem);
  USE_ALLOCATOR(Problem);

  explicit Problem(UnitList* units=0);
  explicit Problem(ClauseIterator clauses, bool copy);
  ~Problem();

  void addUnits(UnitList* newUnits);

  UnitList*& units() { return _units; }
  const UnitList* units() const { return _units; }

  ClauseIterator clauseIterator() const;

  Problem* copy(bool copyClauses=false);
  void copyInto(Problem& tgt, bool copyClauses=false);

  bool hadIncompleteTransformation() const { return _hadIncompleteTransformation; }
  void reportIncompleteTransformation() { _hadIncompleteTransformation = true; }

  typedef DHMap<unsigned,bool> TrivialPredicateMap;
  void addTrivialPredicate(unsigned pred, bool assignment);
  /**
   * Return map of trivial predicates into their assignments.
   *
   * Trivial predicates are the predicates whose all occurrences
   * can be assigned either true or false.
   */
  const TrivialPredicateMap& trivialPredicates() const { return _trivialPredicates; }

  /**
   * Always exactly one of the pair is non-zero, if the literal is specified,
   * it must be ground.
   */
  typedef pair<Literal*,Clause*> BDDMeaningSpec;
  typedef DHMap<unsigned, BDDMeaningSpec> BDDVarMeaningMap;
  void addBDDVarMeaning(unsigned var, BDDMeaningSpec spec);
  const BDDVarMeaningMap& getBDDVarMeanings() const { return _bddVarSpecs; }

  void addEliminatedFunction(unsigned func, Literal* definition);
  void addEliminatedPredicate(unsigned pred, Unit* definition);
  void addPartiallyEliminatedPredicate(unsigned pred, Unit* definition); 
 
  DHMap<unsigned,Literal*> getEliminatedFunctions(){ return _deletedFunctions; }
  DHMap<unsigned,Unit*> getEliminatedPredicates(){ return _deletedPredicates; }
  DHMap<unsigned,Unit*> getPartiallyEliminatedPredicates(){ return _partiallyDeletedPredicates;}
  

  bool isPropertyUpToDate() const { return _propertyValid; }
  Property* getProperty() const;
  void invalidateProperty() { _propertyValid = false; }

  void invalidateByRemoval();
  void invalidateEverything();

  bool hasFormulas() const;
  bool hasEquality() const;
  /** Problem contains an interpreted symbol including equality */
  bool hasInterpretedOperations() const;
  bool hasNumerals() const; // meaning the interpreted constants of arithmetic theories, e.g. 1,2, 3.1415,...
  /** Problem contains let terms or formulas, or term if-then-else */
  bool hasFOOL() const;
  bool hasCombs() const;
  bool hasLogicalProxy() const;
  bool hasBoolVar() const;
  bool hasApp() const;
  bool hasAppliedVar() const;
  bool hasPolymorphicSym() const;
  bool quantifiesOverPolymorphicVar() const;
  bool higherOrder() const;

  bool mayHaveEquality() const { return _mayHaveEquality; }
  bool mayHaveFormulas() const { return _mayHaveFormulas; }
  bool mayHaveFunctionDefinitions() const { return _mayHaveFunctionDefinitions; }
  bool mayHaveInequalityResolvableWithDeletion() const { return _mayHaveInequalityResolvableWithDeletion; }
  bool mayHaveXEqualsY() const { return _mayHaveXEqualsY; }

  void setSMTLIBLogic(SMTLIBLogic smtLibLogic) { 
    _smtlibLogic = smtLibLogic;
  }
  SMTLIBLogic getSMTLIBLogic() const {
    CALL("Kernel::Problem::getSMTLIBLogic");
    return _smtlibLogic;
  }

  void reportFOOLEliminated()
  {
    invalidateProperty();
    _hasFOOL = false;
  }

  void reportFOOLAdded()
  {
    invalidateProperty();
    _hasFOOL = true;
  }
  
  void reportFormulasAdded()
  {
    invalidateProperty();
    _mayHaveFormulas = true;
    _hasFormulas = true;
  }
  /**
   * Report that equality was added into the problem
   *
   * If @c oneVariable is true, the equality contained at least one variable,
   * if @c twoVariables is true, the equality was between two variables
   */
  void reportEqualityAdded(bool oneVariable, bool twoVariables=false)
  {
    invalidateProperty();
    _hasEquality = true;
    _mayHaveEquality = true;
    if(oneVariable) {
      _mayHaveInequalityResolvableWithDeletion = true;
    }
    if(twoVariables) {
      _mayHaveXEqualsY = true;
    }
  }
  void reportFormulasEliminated()
  {
    invalidateProperty();
    _hasFormulas = false;
    _mayHaveFormulas = false;
  }
  void reportEqualityEliminated()
  {
    invalidateProperty();
    _hasEquality = false;
    _mayHaveEquality = false;
    _mayHaveFunctionDefinitions = false;
    _mayHaveInequalityResolvableWithDeletion = false;
    _mayHaveXEqualsY = false;
  }


  //utility functions

  void collectPredicates(Stack<unsigned>& acc) const;


#if VDEBUG
  //debugging functions
  void assertValid();
#endif

private:

  void initValues();

  void refreshProperty() const;
  void readDetailsFromProperty() const;

  UnitList* _units;
  DHMap<unsigned,Literal*> _deletedFunctions;
  DHMap<unsigned,Unit*> _deletedPredicates;
  DHMap<unsigned,Unit*> _partiallyDeletedPredicates; 

  bool _hadIncompleteTransformation;

  DHMap<unsigned,bool> _trivialPredicates;
  BDDVarMeaningMap _bddVarSpecs;

  mutable bool _mayHaveEquality;
  mutable bool _mayHaveFormulas;
  mutable bool _mayHaveFunctionDefinitions;
  mutable bool _mayHaveInequalityResolvableWithDeletion;
  mutable bool _mayHaveXEqualsY;

  mutable MaybeBool _hasFormulas;
  mutable MaybeBool _hasEquality;
  mutable MaybeBool _hasInterpretedOperations;
  mutable MaybeBool _hasNumerals;
  mutable MaybeBool _hasFOOL;
  mutable MaybeBool _hasCombs;
  mutable MaybeBool _hasApp;
  mutable MaybeBool _hasAppliedVar;
  mutable MaybeBool _hasLogicalProxy;
  mutable MaybeBool _hasPolymorphicSym;
  mutable MaybeBool _quantifiesOverPolymorphicVar;
  mutable MaybeBool _hasBoolVar; 
  mutable MaybeBool _higherOrder; 

  SMTLIBLogic _smtlibLogic;

  mutable bool _propertyValid;
  mutable Property* _property;
};

}

#endif // __Kernel_Problem__

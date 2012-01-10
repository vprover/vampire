/**
 * @file Problem.hpp
 * Defines class Problem.
 */

#ifndef __Kernel_Problem__
#define __Kernel_Problem__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/MaybeBool.hpp"



namespace Kernel {

using namespace Lib;
using namespace Shell;

/**
 * Class representing a TPTP problem to be solved
 *
 * The main benefit of this class is that it can carry information about
 * all preprocessing perfored on a problem. This can be necessary for
 * outputing models.
 *
 * Functions has... answer with certainty whether the problem (in its current state)
 * has certain property.
 *
 * Functions mayHave... provide answer that may err on the positive side --
 * for example mayHaveEquality() may return true for a problem that no longer
 * has equality because it was removed somewhere durring preprocessing.
 * These functions are present so that we do not need to keep track of
 * every step performed by the preprocessor, and at the same time we do not
 * need to reevaluate the Property object with each call to such function.
 */
class Problem {
private:
  Problem(const Problem&); //private and undefined copy constructor
  Problem& operator=(const Problem&); //private and undefined assignment operator
public:

  CLASS_NAME("Problem");
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

  void addEliminatedFunction(unsigned func, Literal* definition);
  void addEliminatedPredicate(unsigned pred, Unit* definition);

  bool isPropertyUpToDate() const { return _propertyValid; }
  Property* getProperty() const;
  void invalidateProperty() { _propertyValid = false; }

  void invalidateByRemoval();
  void invalidateEverything();

  bool hasFormulas() const;
  bool hasEquality() const;
  /** Problem contains an interpreted symbol different from equality */
  bool hasInterpretedOperations() const;
  bool hasFormulaItes() const;
  /** Problem contains let terms or formulas, or term if-then-else */
  bool hasSpecialTermsOrLets() const;

  bool mayHaveEquality() const { return _mayHaveEquality; }
  bool mayHaveFormulas() const { return _mayHaveFormulas; }
  bool mayHaveFunctionDefinitions() const { return _mayHaveFunctionDefinitions; }
  bool mayHaveInequalityResolvableWithDeletion() const { return _mayHaveInequalityResolvableWithDeletion; }
  bool mayHaveXEqualsY() const { return _mayHaveXEqualsY; }


  void reportSpecialTermsAndLetsEliminated()
  {
    invalidateProperty();
    _hasSpecialTermsOrLets = false;
  }
  void reportFormulaIteEliminated()
  {
    invalidateProperty();
    _hasFormulaItes = false;
  }
  void reportFormulaIteAdded()
  {
    invalidateProperty();
    _hasFormulaItes = true;
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

private:

  void initValues();

  void refreshProperty() const;
  void readDetailsFromProperty() const;

  UnitList* _units;

  bool _hadIncompleteTransformation;

  DHMap<unsigned,bool> _trivialPredicates;

  mutable bool _mayHaveEquality;
  mutable bool _mayHaveFormulas;
  mutable bool _mayHaveFunctionDefinitions;
  mutable bool _mayHaveInequalityResolvableWithDeletion;
  mutable bool _mayHaveXEqualsY;

  mutable MaybeBool _hasFormulas;
  mutable MaybeBool _hasEquality;
  mutable MaybeBool _hasInterpretedOperations;
  mutable MaybeBool _hasSpecialTermsOrLets;
  mutable MaybeBool _hasFormulaItes;

  mutable bool _propertyValid;
  mutable Property* _property;
};

}

#endif // __Kernel_Problem__

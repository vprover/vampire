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

#include "Lib/MaybeBool.hpp"
#include "Lib/ScopedPtr.hpp"
#include "Lib/Stack.hpp"

#include "Shell/SMTLIBLogic.hpp"

#include "Kernel/Formula.hpp"

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

  enum class IntereferenceKind : unsigned char {
    FUN_DEF = 0,
    PRED_DEF = 1,
    GLOB_FLIP = 2,  // backs up random_polarities
    COND_FLIP = 3,  // backs up partially eliminated predicates (Plaisted-Greenbaum-style p<=>q reduced to, e.g. p=>q) and eliminated blocked clauses
  };

  /* Interference (satisfiability-preserving-only transformations) recording */
  struct Interference {
    IntereferenceKind _kind;
    Interference(IntereferenceKind kind) : _kind(kind) {}

    virtual void outputDefinition(std::ostream&) = 0;
  };

  struct FunDef : public Interference {
    Term* _head;
    Term* _body;
    FunDef(Term* head, Term* body) : Interference(IntereferenceKind::FUN_DEF), _head(head), _body(body) {}

    void outputDefinition(std::ostream&) override;
  };

  struct PredDef : public Interference {
    Literal* _head;
    Formula* _body;
    PredDef(Literal* head, Formula* body) : Interference(IntereferenceKind::PRED_DEF), _head(head), _body(body) {}

    void outputDefinition(std::ostream&) override;
  };

  struct GlobalFlip : public Interference {
    unsigned _pred;

    GlobalFlip(unsigned pred) : Interference(IntereferenceKind::GLOB_FLIP), _pred(pred) {}

    void outputDefinition(std::ostream&) override;
  };

  struct CondFlip : public Interference {
    Formula* _cond;
    bool _neg;
    Literal* _val;
    bool _fixedPoint;

    CondFlip(Formula* cond, bool neg, Literal* val, bool fixedPoint = false)
      : Interference(IntereferenceKind::COND_FLIP), _cond(cond), _neg(neg), _val(val), _fixedPoint(fixedPoint) {}

    void outputDefinition(std::ostream&) override;
  };

  /**
   * Pushing here during preprocessing,
   * replaying backwards to get a model of the original signature.
  */
  Stack<Interference*> interferences;

  void addTrivialPredicate(unsigned pred, bool assignment);
  void addPartiallyEliminatedPredicate(unsigned pred, Formula* remainingImplication);
  void addEliminatedPredicate(unsigned pred, Formula* definition);
  void addFlippedPredicate(unsigned pred);
  void addEliminatedFunction(unsigned func, Literal* definition);
  void addEliminatedBlockedClause(Clause* cl, unsigned blockedLiteralIndex);

  FunctionDefinitionHandler& getFunctionDefinitionHandler(){ return *_fnDefHandler; }

  bool isPropertyUpToDate() const { return _propertyValid; }
  Property* getProperty() const;
  void invalidateProperty() { _propertyValid = false; }

  void invalidateByRemoval();
  void invalidateEverything();

  bool hasFormulas() const;
  bool hasEquality() const;
  bool hasAlascaArithmetic() const;
  bool hasAlascaMixedArithmetic() const;
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
  bool isHigherOrder() const;
  bool hasNonDefaultSorts() const;

  bool mayHaveEquality() const { return _mayHaveEquality; }
  bool mayHaveFormulas() const { return _mayHaveFormulas; }
  bool mayHaveFunctionDefinitions() const { return _mayHaveFunctionDefinitions; }
  bool mayHaveInequalityResolvableWithDeletion() const { return _mayHaveInequalityResolvableWithDeletion; }
  bool mayHaveXEqualsY() const { return _mayHaveXEqualsY; }

  void setSMTLIBLogic(SMTLIBLogic smtLibLogic) {
    _smtlibLogic = smtLibLogic;
  }
  SMTLIBLogic getSMTLIBLogic() const {
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

#if VDEBUG
  //debugging functions
  void assertValid();
#endif

private:

  void initValues();

  void refreshProperty() const;
  void readDetailsFromProperty() const;

  UnitList* _units;
  ScopedPtr<FunctionDefinitionHandler> _fnDefHandler;

  bool _hadIncompleteTransformation;

  mutable bool _mayHaveEquality;
  mutable bool _mayHaveFormulas;
  mutable bool _mayHaveFunctionDefinitions;
  mutable bool _mayHaveInequalityResolvableWithDeletion;
  mutable bool _mayHaveXEqualsY;

  mutable MaybeBool _hasFormulas;
  mutable MaybeBool _hasEquality;
  mutable MaybeBool _hasInterpretedOperations;
  mutable MaybeBool _hasNumerals;
  mutable MaybeBool _hasAlascaArithmetic;
  mutable MaybeBool _hasFOOL;
  mutable MaybeBool _hasApp;
  mutable MaybeBool _hasAppliedVar;
  mutable MaybeBool _hasLogicalProxy;
  mutable MaybeBool _hasPolymorphicSym;
  mutable MaybeBool _quantifiesOverPolymorphicVar;
  mutable MaybeBool _hasBoolVar;
  mutable MaybeBool _higherOrder;
  mutable MaybeBool _hasNonDefaultSorts;

  SMTLIBLogic _smtlibLogic;

  mutable bool _propertyValid;
  mutable Property* _property;
};

}

#endif // __Kernel_Problem__

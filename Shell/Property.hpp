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
 * @file Property.hpp (syntactic properties of problems)
 *
 * @since 06/06/2001 Manchester
 * @since 17/07/2003 Manchester, changed to new representation
 * @since 02/12/2003 Manchester, allocation changed to use Allocator
 * @since 20/05/2007 Manchester, changed to new term representation
 */


#ifndef __Property__
#define __Property__

#include "Lib/DArray.hpp"
#include "Lib/Array.hpp"
#include "Lib/DHSet.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Theory.hpp"
#include "Lib/VString.hpp"
#include "SMTLIBLogic.hpp"

namespace Kernel {
  class Clause;
  class FormulaUnit;
  class Literal;
  class Term;
  class TermList;
  class Formula;
}

namespace Shell {

using namespace std;
using namespace Kernel;
using namespace Lib;

/**
 * Represents syntactic properties of problems.
 */
class Property
{
public:
  /**
   * CASC category
   */
  enum Category {
    NEQ,
    HEQ,
    PEQ,
    HNE,
    NNE,
    FEQ,
    FNE,
    EPR,
    UEQ
  };

  // Various boolean properties.
  /** CNF of the problem has a positive literal x=y */
  static const uint64_t PR_HAS_X_EQUALS_Y = 1ul; // 2^0
  /** Problem has function definitions f(X) = t[X] */
  static const uint64_t PR_HAS_FUNCTION_DEFINITIONS = 2ul; // 2^1
  /** Problem contains a subset axiom */
  static const uint64_t PR_HAS_SUBSET = 4ul; // 2^2
  /** Problem contains extensionality axiom */
  static const uint64_t PR_HAS_EXTENSIONALITY = 8ul; // 2^3
  /** Problem contains an axiomatisation of group theory */
  static const uint64_t PR_GROUP = 16ul; // 2^4
  /** Problem contains an axiomatisation of ring theory */
  static const uint64_t PR_RING = 32ul; // 2^5
  /** Problem contains an axiomatisation of robbins algebras */
  static const uint64_t PR_ROBBINS_ALGEBRA = 64ul; // 2^6
  /** Problem contains an axiomatisation of non-associative rings */
  static const uint64_t PR_NA_RING = 128ul; // 2^7
  /** Problem contains an axiomatisation of boolean algebras */
  static const uint64_t PR_BOOLEAN_ALGEBRA = 256ul; // 2^8
  /** Problem contains an axiomatisation of lattice theory */
  static const uint64_t PR_LATTICE = 512ul; // 2^9
  /** Problem contains an axiomatisation of lattice-ordered groups */
  static const uint64_t PR_LO_GROUP = 1024ul; // 2^10
  /** Problem contains an axiomatisation of the B combinator */
  static const uint64_t PR_COMBINATOR_B = 2048ul; // 2^11
  /** Problem contains an axiomatisation of a combinator S,T,O or Q */
  static const uint64_t PR_COMBINATOR = 4096ul; // 2^12
  /** Problem contains the condensed detachment axiom
   *  ~theorem(X) \/ ~theorem(imply(X,Y)) \/ theorem(Y) */
  static const uint64_t PR_HAS_CONDENSED_DETACHMENT1 = 8192ul; // 2^13
  /** Problem contains the condensed detachment axiom
   *  ~theorem(X) \/ ~theorem(or(not(X),Y)) \/ theorem(Y) */
  static const uint64_t PR_HAS_CONDENSED_DETACHMENT2 = 16384ul; // 2^14
  /** field axioms from TPTP */
  static const uint64_t PR_HAS_FLD1 = 32768ul; // 2^15
  /** other field axioms from TPTP */
  static const uint64_t PR_HAS_FLD2 = 65536ul; // 2^16
  /** Problem contains literal X=t with t non-containing X */
  static const uint64_t PR_HAS_INEQUALITY_RESOLVABLE_WITH_DELETION = 131072ul; // 2^17
  /** Uses string sort */
  static const uint64_t PR_HAS_STRINGS = 262144ul; // 2^18
  /** Uses integer sort */
  static const uint64_t PR_HAS_INTEGERS = 524288ul; // 2^19
  /** Uses rational sort */
  static const uint64_t PR_HAS_RATS = 1048576ul; // 2^20
  /** Uses real sort */
  static const uint64_t PR_HAS_REALS = 2097152ul; // 2^21
  /** Has sort declarations */
  static const uint64_t PR_SORTS = 4194304ul; // 2^22
  /** Uses integer comparisons $less, $lesseq, $greater, $greatereq */
  static const uint64_t PR_INTEGER_COMPARISON = 8388608ul; // 2^23
  /** Uses rational comparisons $less, $lesseq, $greater, $greatereq */
  static const uint64_t PR_RAT_COMPARISON = 16777216ul; // 2^24
  /** Uses real comparisons $less, $lesseq, $greater, $greatereq */
  static const uint64_t PR_REAL_COMPARISON = 33554432ul; // 2^25
  /** Uses integer functions $uminus,$sum,$difference */
  static const uint64_t PR_INTEGER_LINEAR = 67108864ul; // 2^26
  /** Uses rational functions $uminus,$sum,$difference */
  static const uint64_t PR_RAT_LINEAR = 134217728ul; // 2^27
  /** Uses real functions $uminus,$sum,$difference */
  static const uint64_t PR_REAL_LINEAR = 268435456ul; // 2^28
  /** Uses integer non-linear functions $product,$quotient,$remainder */
  static const uint64_t PR_INTEGER_NONLINEAR = 536870912ul; // 2^29
  /** Uses integer non-linear functions $product,$quotient,$remainder */
  static const uint64_t PR_RAT_NONLINEAR = 1073741824ul; // 2^30
  /** Uses integer non-linear functions $product,$quotient,$remainder */
  static const uint64_t PR_REAL_NONLINEAR = 2147483648ul; // 2^31
  /** Uses number conversion functions $floor, $ceiling, $truncate, $round, $is_int, $is_rat, $to_int, $to_int, $to_rat, $to_real */
  static const uint64_t PR_NUMBER_CONVERSION = 4294967296ul; // 2^32
  /** when skolemised, will become ground, probably useless */
  static const uint64_t PR_ESSENTIALLY_GROUND = 8589934592ul; // 2^33
  /** uses list axioms */
  static const uint64_t PR_LIST_AXIOMS = 17179869184ul; // 2^34
  /** uses boolean variables */
  static const uint64_t PR_HAS_BOOLEAN_VARIABLES =  34359738368ul; // 2^35
  /** uses Arrays, should these be split? */
  static const uint64_t PR_HAS_ARRAYS = 68719476736ul; // 2^36
  /** has a finite domain axiom */
  static const uint64_t PR_HAS_FINITE_DOMAIN = 137438953472ul; // 2^37
  /** has if-then-else */
  static const uint64_t PR_HAS_ITE = 274877906944ul; // 2^38
  /** has let-in */
  static const uint64_t PR_HAS_LET_IN = 549755813888ul; // 2^39
  /* has data type constructors */
  static const uint64_t PR_HAS_DT_CONSTRUCTORS = 1099511627776ul; // 2^40
  /* has co-algrebaic data type constructors */
  static const uint64_t PR_HAS_CDT_CONSTRUCTORS = 2199023255552ul; // 2^41

 public:
  CLASS_NAME(Property);
  USE_ALLOCATOR(Property);

  // constructor, operators new and delete
  explicit Property();
  static Property* scan(UnitList*);
  void add(UnitList*);
  ~Property();

  /** Return the CASC category of the problem */
  Category category() const { return _category;}
  static vstring categoryToString(Category cat);
  vstring categoryString() const;

  vstring toString() const;
  vstring toSpider(const vstring& problemName) const;

  /** Total number of clauses in the problem. */
  int clauses() const { return _goalClauses + _axiomClauses; }
  /** Total number of formulas in the problem */
  int formulas() const { return _goalFormulas + _axiomFormulas; }
  /** Total number of unit clauses in the problem */
  int unitClauses() const { return _unitGoals + _unitAxioms; }
  /** Total number of Horn clauses in the problem */
  int hornClauses() const { return _hornGoals + _hornAxioms; }
  /** Total number of atoms in the problem */
  int atoms() const { return _atoms; }
  /** Total number of equality atoms in the problem */
  int equalityAtoms() const { return _equalityAtoms; }
  /** Total number of positive equality atoms in the problem, does not work correctly
      with formulas since polarity is not taken into account */
  int positiveEqualityAtoms() const { return _positiveEqualityAtoms; }
  /** True if has formulas */
  bool hasFormulas() const { return _axiomFormulas || _goalFormulas; }
  /** Maximal arity of a function in the problem */
  int maxFunArity() const { return _maxFunArity; }
  /** Maximal arity of a type con in the problem */
  unsigned maxTypeConArity() const { return _maxTypeConArity; }
  /** Total number of variables in problem */
  int totalNumberOfVariables() const { return _totalNumberOfVariables;}

  /** The problem has property p */
  bool hasProp(uint64_t p) const { return _props & p; }
  /** Add property p to the list of properties */
  void addProp(uint64_t p) { _props |= p; }
  /** Remove a property from the list of properties */
  void dropProp(uint64_t p) { _props &= ~p; }
  /** Return props as an integer, mainly for debugging */
  uint64_t props() const { return _props; }

  /**
   * To be used from outside of the Property class when a preprocessing
   * rule may add into problem new operation
   *
   * @c t may be either a term or a literal
   */
  void scanForInterpreted(Term* t);

  bool hasInterpretedOperation(Interpretation i) const {
    if(i >= _interpretationPresence.size()){ return false; }
    return _interpretationPresence[i]; 
  }
  bool hasInterpretedOperation(Interpretation i, OperatorType* type) const {
    return _polymorphicInterpretations.find(std::make_pair(i,type));
  }

  /** Problem contains an interpreted symbol excluding equality */
  bool hasInterpretedOperations() const { return _hasInterpreted; }
  bool hasNumerals() const { return hasProp(PR_HAS_INTEGERS) || hasProp(PR_HAS_REALS) || hasProp(PR_HAS_RATS); }
  bool hasGoal() const { return _goalClauses > 0 || _goalFormulas > 0; }
  /** Problem contains non-default sorts */
  bool hasNonDefaultSorts() const { return _hasNonDefaultSorts; }
  bool hasFOOL() const { return _hasFOOL; }
  bool hasCombs() const { return _hasCombs;}
  bool hasApp() const { return _hasApp; }
  bool hasAppliedVar() const { return _hasAppliedVar; }
  bool hasBoolVar() const { return _hasBoolVar; }
  bool hasLogicalProxy() const { return _hasLogicalProxy; }
  bool hasPolymorphicSym() const { return _hasPolymorphicSym; }
  bool higherOrder() const { return hasCombs() || hasApp() || hasLogicalProxy() || _hasLambda; }
  bool quantifiesOverPolymorphicVar() const { return _quantifiesOverPolymorphicVar; }
  bool usesSort(unsigned sort) const { 
    CALL("Property::usesSort");
    if(_usesSort.size() <= sort) return false;
    return _usesSort[sort]; 
  } //TODO only utilised by FMB which should eventually update to use the new sorts (as TermLists)
  bool usesSingleSort() const { return _sortsUsed==1; }
  unsigned sortsUsed() const { return _sortsUsed; }
  bool onlyFiniteDomainDatatypes() const { return _onlyFiniteDomainDatatypes; }
  bool knownInfiniteDomain() const { return _knownInfiniteDomain; }
  
  void setSMTLIBLogic(SMTLIBLogic smtLibLogic) { 
    CALL("Property::setSMTLIBLogic");
    _smtlibLogic = smtLibLogic; 
  }
  SMTLIBLogic getSMTLIBLogic() const { 
    return _smtlibLogic; 
  }

  bool allNonTheoryClausesGround(){ return _allNonTheoryClausesGround; }

 private:
  static bool hasXEqualsY(const Clause* c);
  static bool hasXEqualsY(const Formula*);

  // reading in properties of problems
  void scan(Unit*);

  // these two are the only ones which start the deep iteration
  void scan(Clause*);
  void scan(FormulaUnit*);

  void scan(Literal* lit, int polarity, unsigned cLen, bool goal);
  void scan(Formula*, int polarity);
  void scan(TermList ts,bool unit,bool goal);

  void scanSort(TermList sort);

  // structure
  int _goalClauses;
  int _axiomClauses;

  int _positiveEqualityAtoms;
  int _equalityAtoms;
  int _atoms;

  int _goalFormulas;
  int _axiomFormulas;
  int _subformulas;

  int _unitGoals;
  int _unitAxioms;
  int _hornGoals;
  int _hornAxioms;
  int _equationalClauses;
  int _pureEquationalClauses;
  int _groundUnitAxioms;
  int _positiveAxioms;
  int _groundPositiveAxioms;
  int _groundGoals;
  int _maxFunArity;
  int _maxPredArity;
  unsigned _maxTypeConArity;

  /** Number of variables in this clause, used during counting */
  int _variablesInThisClause;
  /** Total number of variables in all clauses */
  int _totalNumberOfVariables;
  /** Maximal number of variables in a clause */
  int _maxVariablesInClause;
  /** Symbols in this formula, used during counting 
      Functions are positive, predicates stored in the negative part
  **/
  DHSet<int> _symbolsInFormula;

  /** Bitwise OR of all properties of this problem */
  uint64_t _props;

  /** CASC category of the problem, computed by read() */
  Category _category;

  /** Problem contains an interpreted symbol including equality */
  bool _hasInterpreted;
  /** Problem contains non-default sorts */
  bool _hasNonDefaultSorts;
  unsigned _sortsUsed;
  Array<bool> _usesSort;

  /** Makes sense for all interpretations, but for polymorphic ones we also keep
   *  the more precise information about which monomorphisations are present (see below).
   */
  DArray<bool> _interpretationPresence;
  DHSet<Theory::MonomorphisedInterpretation> _polymorphicInterpretations;

  bool _hasFOOL;
  bool _hasCombs;
  bool _hasApp;
  bool _hasAppliedVar;
  bool _hasBoolVar;
  bool _hasLogicalProxy;
  bool _hasLambda;
  bool _hasPolymorphicSym;
  bool _quantifiesOverPolymorphicVar;

  bool _onlyFiniteDomainDatatypes;
  bool _knownInfiniteDomain;

  bool _allClausesGround;
  bool _allNonTheoryClausesGround;
  bool _allQuantifiersEssentiallyExistential;
  SMTLIBLogic _smtlibLogic;
}; // class Property

}

#endif // __Property__

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

#include <string>

#include "Lib/DArray.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Theory.hpp"

namespace Lib {
  class MultiCounter;
}

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
  static const unsigned PR_HAS_X_EQUALS_Y = 1u; // 2^0
  /** Problem has function definitions f(X) = t[X] */
  static const unsigned PR_HAS_FUNCTION_DEFINITIONS = 2u; // 2^1
  /** Problem contains a subset axiom */
  static const unsigned PR_HAS_SUBSET = 4u; // 2^2
  /** Problem contains extensionality axiom */
  static const unsigned PR_HAS_EXTENSIONALITY = 8u; // 2^3
  /** Problem contains an axiomatisation of group theory */
  static const unsigned PR_GROUP = 16u; // 2^4
  /** Problem contains an axiomatisation of ring theory */
  static const unsigned PR_RING = 32u; // 2^5
  /** Problem contains an axiomatisation of robbins algebras */
  static const unsigned PR_ROBBINS_ALGEBRA = 64u; // 2^6
  /** Problem contains an axiomatisation of non-associative rings */
  static const unsigned PR_NA_RING = 128u; // 2^7
  /** Problem contains an axiomatisation of boolean algebras */
  static const unsigned PR_BOOLEAN_ALGEBRA = 256u; // 2^8
  /** Problem contains an axiomatisation of lattice theory */
  static const unsigned PR_LATTICE = 512u; // 2^9
  /** Problem contains an axiomatisation of lattice-ordered groups */
  static const unsigned PR_LO_GROUP = 1024u; // 2^10
  /** Problem contains an axiomatisation of the B combinator */
  static const unsigned PR_COMBINATOR_B = 2048u; // 2^11
  /** Problem contains an axiomatisation of a combinator S,T,O or Q */
  static const unsigned PR_COMBINATOR = 4096u; // 2^12
  /** Problem contains the condensed detachment axiom
   *  ~theorem(X) \/ ~theorem(imply(X,Y)) \/ theorem(Y) */
  static const unsigned PR_HAS_CONDENSED_DETACHMENT1 = 8192u; // 2^13
  /** Problem contains the condensed detachment axiom
   *  ~theorem(X) \/ ~theorem(or(not(X),Y)) \/ theorem(Y) */
  static const unsigned PR_HAS_CONDENSED_DETACHMENT2 = 16384u; // 2^14
  /** field axioms from TPTP */
  static const unsigned PR_HAS_FLD1 = 32768u; // 2^15
  /** other field axioms from TPTP */
  static const unsigned PR_HAS_FLD2 = 65536u; // 2^16
  /** Problem contains literal X=t with t non-containing X */
  static const unsigned PR_HAS_INEQUALITY_RESOLVABLE_WITH_DELETION = 131072u; // 2^17
  /** Has strings */
  static const unsigned PR_HAS_STRINGS = 262144u; // 2^18
  /** Has integer sort */
  static const unsigned PR_HAS_INTEGERS = 524288u; // 2^19
  /** Has rational sort */
  static const unsigned PR_HAS_RATS = 1048576u; // 2^20
  /** Has real sort */
  static const unsigned PR_HAS_REALS = 2097152u; // 2^21
  /** Has sort declarations */
  static const unsigned PR_SORTS = 4194304u; // 2^22
  /** Has array1 sorts and operations*/
  static const unsigned PR_HAS_ARRAYS1 = 8388608u; // 2^23
  /** Has array2 sorts and operations*/
  static const unsigned PR_HAS_ARRAYS2 = 16777216u; // 2^24
// 33554432u; // 2^25
// 67108864u; // 2^26
// 134217728u; // 2^27
// 268435456u; // 2^28
// 536870912u; // 2^29
// 1073741824u; // 2^30

 public:
  CLASS_NAME(Property);
  USE_ALLOCATOR(Property);

  static Property* scan(UnitList*);
  void add(UnitList*);
  ~Property();

  /** Return the CASC category of the problem */
  Category category() const { return _category;}
  string categoryString() const;

  string toString() const;
  string toSpider(const string& problemName) const;

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


  /** The problem has property p */
  bool hasProp(unsigned p) const { return _props & p; }
  /** Add property p to the list of properties */
  void addProp(unsigned p) { _props |= p; }
  /** Return props as an integer, mainly for debugging */
  unsigned int props() const { return _props; }

  /**
   * To be used from outside of the Property class when a preprocessing
   * rule may add into problem new operation
   *
   * @c t may be either a term or a literal
   */
  void scanForInterpreted(Term* t);

  bool hasInterpretedOperation(Interpretation i) const { return _interpretationPresence[i]; }
  //bool hasArrayOperation(Interpretation i) const { return true; }
  /** Problem contains an interpreted symbol different from equality */
  bool hasInterpretedOperations() const { return _hasInterpreted; }
  /** Problem contains non-default sorts */
  bool hasNonDefaultSorts() const { return _hasNonDefaultSorts; }
  bool hasSpecialTermsOrLets() const { return _hasSpecialTermsOrLets; }
  bool hasFormulaItes() const { return _hasFormulaItes; }
 private:
  // constructor, operators new and delete
  explicit Property();

  static bool hasXEqualsY(const Clause* c);
  static bool isXEqualsY(const Literal*,bool polarity);
  static bool hasXEqualsY(const Formula*, MultiCounter&, int polarity);

  // reading in properties of problems
  void scan(Unit*);
  void scan(Clause*);
  void scan(FormulaUnit*);
  void scan(Formula*);
  void scan(TermList* ts);
  void scan(Literal* lit);
  void scanSpecialTerm(Term* t);
  void scanSort(unsigned sort);

  char axiomTypes() const;
  char goalTypes() const;
  char equalityContent() const;
  char nonGroundUnitContent() const;
  char groundPositiveContent() const;
  char goalsAreGround() const;
  char setClauseSize() const;
  char setLiteralSize() const;
  char setTermSize() const;
  char maxPredArity() const;

  // structure
  int _goalClauses;
  int _axiomClauses;

  int _positiveEqualityAtoms;
  int _equalityAtoms;
  int _atoms;

  int _goalFormulas;
  int _axiomFormulas;
  int _subformulas;

  int _terms;
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

  /** Number of variables in this clause, used during counting */
  int _variablesInThisClause;
  /** Total number of variables in all clauses */
  int _totalNumberOfVariables;
  /** Maximal number of variables in a clause */
  int _maxVariablesInClause;

  /** Bitwise OR of all properties of this problem */
  unsigned _props;

  /** CASC category of the problem, computed by read() */
  Category _category;

  /** Problem contains an interpreted symbol different from equality */
  bool _hasInterpreted;
  /** Problem contains non-default sorts */
  bool _hasNonDefaultSorts;
  DArray<bool> _interpretationPresence;

  bool _hasSpecialTermsOrLets;
  bool _hasFormulaItes;
}; // class Property

}

#endif // __Property__

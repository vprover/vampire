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

#include "../Kernel/Unit.hpp"

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

using namespace std;
using namespace Kernel;
using namespace Lib;


namespace Shell {

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

  /**
   * Represents various boolean properties. Every Property
   * has an integer _props that is a bitwise OR of all Prop's.
   */
  enum Prop {
    /** CNF of the problem has a positive literal x=y */
    PR_HAS_X_EQUALS_Y = 1u,
    /** Problem has function definitions f(X) = t[X] */
    PR_HAS_FUNCTION_DEFINITIONS = 2u,
    /** Problem contains a subset axiom */
    PR_HAS_SUBSET = 4u,
    /** Problem contains extensionality axiom */
    PR_HAS_EXTENSIONALITY = 8u,
    /** Problem contains an axiomatisation of group theory */
    PR_GROUP = 16u,
    /** Problem contains an axiomatisation of ring theory */
    PR_RING = 32u,
    /** Problem contains an axiomatisation of robbins algebras */
    PR_ROBBINS_ALGEBRA = 64u,
    /** Problem contains an axiomatisation of non-associative rings */
    PR_NA_RING = 128u,
    /** Problem contains an axiomatisation of boolean algebras */
    PR_BOOLEAN_ALGEBRA = 256u,
    /** Problem contains an axiomatisation of lattice theory */
    PR_LATTICE = 512u,
    /** Problem contains an axiomatisation of lattice-ordered groups */
    PR_LO_GROUP = 1024u,
    /** Problem contains an axiomatisation of the B combinator */
    PR_COMBINATOR_B = 2048u,
    /** Problem contains an axiomatisation of a combinator S,T,O or Q */
    PR_COMBINATOR = 4096u,
    /** Problem contains the condensed detachment axiom
     *  ~theorem(X) \/ ~theorem(imply(X,Y)) \/ theorem(Y) */
    PR_HAS_CONDENSED_DETACHMENT1 = 8192u,
    /** Problem contains the condensed detachment axiom
     *  ~theorem(X) \/ ~theorem(or(not(X),Y)) \/ theorem(Y) */
    PR_HAS_CONDENSED_DETACHMENT2 = 16384u,
    PR_HAS_FLD1                  = 32768u,
    PR_HAS_FLD2                  = 65536u,
    /** Problem contains literal X=t with t non-containing X */
    PR_HAS_INEQUALITY_RESOLVABLE_WITH_DELETION = 131072u
  };

 public:
  // constructor
  explicit Property ();
  void scan(UnitList*);

  /** Return the CASC category of the problem */
  Category category() const { return _category;}
  string categoryString() const;

  string toString () const;
  string toSpider (const string& problemName) const;

  /** Total number of clauses in the problem. */
  int clauses () const { return _goalClauses + _axiomClauses; }
  /** Total number of formulas in the problem */
  int formulas () const { return _goalFormulas + _axiomFormulas; }
  /** Total number of unit clauses in the problem */
  int unitClauses () const { return _unitGoals + _unitAxioms; }
  /** Total number of Horn clauses in the problem */
  int hornClauses () const { return _hornGoals + _hornAxioms; }
  /** Total number of atoms in the problem */
  int atoms() const { return _atoms; }
  /** Total number of equality atoms in the problem */
  int equalityAtoms() const { return _equalityAtoms; }
  /** Total number of positive equality atoms in the problem */
  int positiveEqualityAtoms() const { return _positiveEqualityAtoms; }
  /** True if has formulas */
  bool hasFormulas () const { return _axiomFormulas || _goalFormulas; }

  /** The problem has property p */
  bool hasProp (Prop p) const { return _props & p; }
  /** Add property p to the list of properties */
  void addProp (Prop p) { _props |= p; }
  /** Return props as an integer, mainly for debugging */
  unsigned int props () const { return _props; }

 private:
  static bool hasXEqualsY (const Clause* c);
  static bool isXEqualsY (const Literal*,bool polarity);
  static bool hasXEqualsY (const Formula*, MultiCounter&, int polarity);

  // reading in properties of problems
  void scan(Unit*);
  void scan(Clause*);
  void scan(FormulaUnit*);
  void scan(Formula*);
  void scan(TermList* ts,bool& isGround);
  void scan(Literal* lit,bool& isGround);

  char axiomTypes () const;
  char goalTypes () const;
  char equalityContent () const;
  char nonGroundUnitContent () const;
  char groundPositiveContent () const;
  char goalsAreGround () const;
  char setClauseSize () const;
  char setLiteralSize () const;
  char setTermSize () const;
  char maxFunArity () const;
  char maxPredArity () const;

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
}; // class Property

}

#endif // __Property__

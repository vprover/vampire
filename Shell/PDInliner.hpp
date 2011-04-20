/**
 * @file PDInliner.hpp
 * Defines class PDInliner for inlining of predicate definitions.
 */

#ifndef __PDInliner__
#define __PDInliner__

#include "Forwards.hpp"

#include "Lib/Array.hpp"
#include "Lib/DArray.hpp"
#include "Lib/Set.hpp"

namespace Shell {

using namespace Lib;
using namespace Kernel;

/**
 * Preprocessing rule that performs predicate definition inlining
 *
 * Application of predicate definition inlining can turn clauses into general formulas
 */
class PDInliner {
public:
  PDInliner(bool axiomsOnly);
  ~PDInliner();

  /**
   * Apply predicate definition inlining
   *
   * The units must be rectified before passing to this function, they will
   * remain rectified afterward.
   *
   * The rule preserves flattening and true/false simplifiedness of formulas.
   */
  void apply(UnitList*& units);
  Unit* apply(Unit* u);

  /**
   * Attempt to extract definition from formula @c unit, and return true iff
   * successful.
   */
  bool tryGetDef(FormulaUnit* unit);

  bool tryGetPredicateEquivalence(FormulaUnit* unit);

private:

  struct Applicator;
  struct PDef;

  bool isEligible(FormulaUnit* u);

  void scanAndRemoveDefinitions(UnitList*& units);
  bool tryGetDef(FormulaUnit* unit, Literal* lhs, Formula* rhs);

  static bool isPredicateEquivalence(FormulaUnit* u, unsigned& pred1, unsigned& pred2);
  static bool isDefinitionHead(Literal* l);

  ZIArray<PDef*> _defs;
  /**
   * For each predicate the array contains set of defined predicates that
   * depend on it.
   *
   * Invariant: For each predicate p either _defs[p]==0 or _dependent[p] is empty.
   * This holds because we inline predicate definitions into other definitions as
   * soon as we discover them, and inlining removes the dependency.
   */
  DArray<Set<unsigned> > _dependent;

  bool _axiomsOnly;
};

}

#endif // __PDInliner__

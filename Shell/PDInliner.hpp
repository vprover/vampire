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
  PDInliner(bool axiomsOnly=false, bool trace=false, bool nonGrowing=false);
  ~PDInliner();

  void apply(Problem& prb);

  /**
   * Apply predicate definition inlining
   *
   * The units must be rectified before passing to this function, they will
   * remain rectified afterward.
   *
   * The rule preserves flattening and true/false simplifiedness of formulas.
   *
   * Return true iff some unit was modified.
   */
  bool apply(UnitList*& units, bool inlineOnlyEquivalences=false);
  Unit* apply(Unit* u);
  FormulaUnit* apply(FormulaUnit* u);

  /**
   * Attempt to extract definition from formula @c unit, and return true iff
   * successful.
   *
   * If @c isEligible() returns false on @c unit, false is returned without
   * attempts to extract definition.
   */
  bool tryGetDef(FormulaUnit* unit);
  /**
   * Extract definition from @c unit, specifying wat is LHS and what RHS.
   */
  bool tryGetDef(FormulaUnit* unit, Literal* lhs, Formula* rhs);

  bool tryGetPredicateEquivalence(FormulaUnit* unit);
  bool scanAndRemoveDefinitions(UnitList*& units, bool equivalencesOnly);

  bool addAsymetricDefinition(Literal* lhs, Formula* posBody, Formula* negBody, Formula* dblBody,
      FormulaUnit* premise=0);
private:

  friend class EPRRestoring;
  friend class EPRInlining;

  struct Applicator;
  struct PDef;

  bool isEligible(FormulaUnit* u);


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
  bool _nonGrowing;
  bool _trace;
};

}

#endif // __PDInliner__

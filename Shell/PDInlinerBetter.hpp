/**
 * @file PDInliner.hpp
 * Defines class PDInliner for inlining of predicate definitions.
 */

#ifndef __PDInliner__
#define __PDInliner__

#include "Forwards.hpp"

#include "Lib/Array.hpp"
#include "Lib/DArray.hpp"
#include "Lib/MultiCounter.hpp"
#include "Lib/SharedSet.hpp"
#include "Lib/Set.hpp"
#include "Lib/Stack.hpp"

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
  PDInliner(bool axiomsOnly=false, bool nonGrowing=false);
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
  Unit* apply(Clause* u);
  FormulaUnit* apply(FormulaUnit* u);

  /**
   * Attempt to extract definition from formula @c unit, and return true iff
   * successful.
   *
   * If @c isEligible() returns false on @c unit, false is returned without
   * attempts to extract definition.
   */
  bool tryGetDef(FormulaUnit* unit);
  bool tryGetPredicateEquivalence(FormulaUnit* unit);
  bool scanAndRemoveDefinitions(UnitList*& units, bool equivalencesOnly);

  void prepareScannedDefs();

  bool addAsymetricDefinition(Literal* lhs, Formula* posBody, Formula* negBody, Formula* dblBody,
      FormulaUnit* premise=0);

  void updatePredOccCounts(Unit* u);
  bool isNonGrowingDef(Literal* lhs, Formula* rhs);

  /**
   * Extract definition from @c unit, specifying what is LHS and what RHS.
   */
  bool tryGetDef(FormulaUnit* unit, Literal* lhs, Formula* rhs);
private:


  typedef SharedSet<unsigned> DepSet;

  friend class EPRRestoring;
  friend class EPRInlining;

  struct Applicator;
  struct DefDep;
  struct PDef;

  struct InliningState
  {
    Stack<Unit*> premises;
    bool needsRectify;
    bool needsConstantSimplification;

    void reset()
    {
      CALL("PDInliner::InliningState::reset");
      premises.reset();
      needsRectify = false;
      needsConstantSimplification = false;
    }
  };

  Formula* apply(int polarity, Formula* form, InliningState& state);
  void getInferenceAndInputType(Unit* transformedUnit, InliningState& state, Inference*& inf, Unit::InputType& inp);


  bool isEligible(FormulaUnit* u);


  static bool isDefinitionHead(Literal* l);

  ZIArray<PDef*> _defs;

  ZIArray<DefDep*> _deps;
  /**
   * For each predicate the array contains set of defined predicates that
   * depend on it.
   *
   * Invariant: For each predicate p either _defs[p]==0 or _dependent[p] is empty.
   * This holds because we inline predicate definitions into other definitions as
   * soon as we discover them, and inlining removes the dependency.
   */
  DArray<Stack<unsigned> > _dependent;

  /**
   * Counts numbers of predicate occurrences.
   * Valid only if _nonGrowing is true (otherwise there
   * is no need to maintain this count).
   *
   * This object is populated in scanAndRemoveDefinitions() during the scan for
   * predicate equivalences.
   */
  MultiCounter _predOccCounts;

  bool _axiomsOnly;
  bool _nonGrowing;
};

}

#endif // __PDInliner__

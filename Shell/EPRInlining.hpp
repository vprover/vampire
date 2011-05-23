/**
 * @file EPRInlining.hpp
 * Defines class EPRInlining.
 */

#ifndef __EPRInlining__
#define __EPRInlining__

#include "Forwards.hpp"

#include "Lib/Array.hpp"
#include "Lib/DArray.hpp"
#include "Lib/Deque.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/MapToLIFO.hpp"
#include "Lib/Set.hpp"
#include "Lib/Stack.hpp"

#include "PDInliner.hpp"


namespace Shell {

class EPRRestoring {
public:
  void scan(UnitList* units);

protected:
  EPRRestoring(bool trace) : _trace(trace) {}

  virtual void processActiveDefinitions(UnitList* units) {}

  static void splitDefinition(FormulaUnit* unit, Literal*& lhs, Formula*& rhs);

  /** for a definition stores predicate defined by it */
  DHMap<Unit*, unsigned> _defPreds;

  /**
   * Active predicates
   *
   * Predicates whose definitions will be inlined in order to restore
   * the EPR.
   *
   * Definitions of the predicates cannot depend on definitions
   * of other predicates that are closer to the top of the stack.
   */
  Stack<unsigned> _activePreds;

  /**
   * Units belonging to active predicates
   */
  DHSet<Unit*> _activeUnits;

  ZIArray<FormulaUnit*> _nonEprDefs;
  /** True if the lhs literal is negative */
  ZIArray<bool> _nonEprReversedPolarity;
  /**
   * For each predicate with non-epr def contains -1, 0 or 1. This means
   * that lhs occurrences with given polarity need to be inlined
   * (zero means both).
   *
   * The important thing is that we mean the polarity of the lhs, not
   * polarity of the predicate -- this can be the reverse in case the
   * lhs contains a negated predicate.
   */
  ZIArray<int> _nonEprDefPolarities;

  bool _trace;
private:
  bool scanDefinition(FormulaUnit* unit);
  void performClosure();

  static bool isNonEPRDef(Literal* lhs, Formula* body, int& polarity);
  static bool hasDefinitionShape(FormulaUnit* unit, Literal* lhs, Formula* rhs);
  static bool hasDefinitionShape(FormulaUnit* unit);
  static int combinePolarities(int p1, int p2);

  bool addNEDef(FormulaUnit* unit, unsigned functor, int polarity);

  Deque<unsigned> _newNEPreds;

  Stack<unsigned> _nonEprPreds;

  typedef MapToLIFO<unsigned,pair<FormulaUnit*,int> > DepMap;

  /** For each predicate contains definitions that contain it, together with the polarity */
  DepMap _dependent;
};

class EPRInlining : public EPRRestoring {
public:
  EPRInlining(bool trace=false) : EPRRestoring(trace), _inliner(false, trace) {}

  Unit* apply(Unit* unit);
  void apply(UnitList*& units);
protected:
  virtual void processActiveDefinitions(UnitList* units);
private:
  PDInliner _inliner;
};

class EPRSkolem : public EPRRestoring {
public:
  EPRSkolem(bool trace=false) : EPRRestoring(trace), _defs(0) {}

  void apply(UnitList*& units);
  bool apply(Unit* unit, UnitList*& res);
protected:
  virtual void processActiveDefinitions(UnitList* units);
private:
  void enableLiteralHeader(unsigned header);
  void processLiteralHeader(Literal* lit, unsigned header);
  void processProblemLiteral(Literal* lit, int polarity);
  void processProblemClause(Clause* cl);
  void processProblemFormula(FormulaUnit* fu);

  void processDefinition(unsigned header);

  bool applyToDefinitionHalf(FormulaUnit* fu, Literal* lhs, Formula* rhs,
      int topPolarity, UnitList*& res);
  void processDefinition(FormulaUnit* unit);

  FormulaUnit* definitionToImplication(FormulaUnit* premise, Literal* lhs,
      Formula* rhs, int topPolarity);

  static string headerToString(unsigned hdr);

  class Applicator;
  class CannotEPRSkolemize : public Exception {};


  typedef MapToLIFO<unsigned,Literal*> InstMap;

  /**
   * Map from literal headers that should have EPR violating
   * definition inlined, to the list of their instances among
   * formulas which aren't active definitions.
   */
  InstMap _insts;

  DHSet<unsigned> _inlinedHeaders;

  /** Set of (EPR inlineable) literal headers that have non-ground
   * instances among formulas which aren't active definitions. */
  DHSet<unsigned> _haveNonground;

  typedef DHMap<Unit*,UnitList*> ReplacementMap;

  /** Map from definitions to their replacements */
  ReplacementMap _replacements;

  UnitList* _defs;
};

}

#endif // __EPRInlining__

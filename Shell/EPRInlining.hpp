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
  virtual ~EPRRestoring() {}
protected:  
  virtual void processActiveDefinitions(UnitList* units) {}


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
  
private:
  bool scanDefinition(FormulaUnit* unit);
  void performClosure();

  static bool isNonEPRDef(Literal* lhs, Formula* body, int& polarity);
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
  EPRInlining() : EPRRestoring(), _inliner(false) {}

  Unit* apply(Unit* unit);
  bool apply(UnitList*& units);
  void apply(Problem& prb);
protected:
  virtual void processActiveDefinitions(UnitList* units);
private:
  PDInliner _inliner;
};

}

#endif // __EPRInlining__

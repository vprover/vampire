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

class EPRInlining {
public:
  EPRInlining(bool trace=false) : _inliner(false, trace), _trace(trace) {}

  void scan(UnitList* units);
  Unit* apply(Unit* unit);
  void apply(UnitList*& units);

private:
  bool scanDefinition(FormulaUnit* unit);

  void performClosure();

  static void splitDefinition(FormulaUnit* unit, Literal*& lhs, Formula*& rhs);
  static bool isNonEPRDef(Literal* lhs, Formula* body, int& polarity);
  static bool hasDefinitionShape(FormulaUnit* unit, Literal* lhs, Formula* rhs);
  static bool hasDefinitionShape(FormulaUnit* unit);
  static int combinePolarities(int p1, int p2);

  bool addNEDef(FormulaUnit* unit, unsigned functor, int polarity);

  DHSet<Unit*> _activeUnits;

  PDInliner _inliner;

  /** for a definition stores predicate defined by it */
  DHMap<Unit*, unsigned> _defPreds;
  Deque<unsigned> _newNEPreds;

  Stack<unsigned> _nonEprPreds;
  ZIArray<FormulaUnit*> _nonEprDefs;
  /** True if the lhs literal is negative */
  ZIArray<bool> _nonEprReversedPolarity;
  /**
   * For each predicate with non-epr def contains -1, 0 or 1. This means
   * that lhs occurrences with given polarity need to be inlined
   * (zero means both).
   */
  ZIArray<int> _nonEprDefPolarities;

  typedef MapToLIFO<unsigned,pair<FormulaUnit*,int> > DepMap;

  /** For each predicate contains definitions that contain it, together with the polarity */
  DepMap _dependent;

  bool _trace;
};

}

#endif // __EPRInlining__

/**
 * @file PDMerger.hpp
 * Defines class PDMerger.
 */

#ifndef __PDMerger__
#define __PDMerger__

#include "Forwards.hpp"

#include "Lib/Comparison.hpp"
#include "Lib/Deque.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/ScopedPtr.hpp"
#include "Lib/Stack.hpp"

#include "Indexing/FormulaIndex.hpp"

#include "PDInliner.hpp"

namespace Shell {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;

class PDMerger {
public:
  PDMerger(bool trace=false);
  ~PDMerger();

  void scan(UnitList* units);
  bool apply(UnitList*& units);
  void apply(Problem& prb);
  Unit* apply(Unit* unit);
  FormulaUnit* apply(FormulaUnit* unit);

private:
  void processDefinition(FormulaUnit* unit);

  void handleIndexes(FormulaUnit* unit, bool insert);
  void triggerNewDefinitions(unsigned elPred);

  class Normalizer;

  struct UnitComparator
  {
    static Comparison compare(Unit* u1, Unit* u2);
  };

  bool _trace;

  ScopedPtr<FormulaIndex> _index;

  DHMap<FormulaUnit*,FormulaUnit*> _replacements;
  PDInliner _inliner;

  typedef Deque<FormulaUnit*> FormulaQueue;

  /**
   * Queue of definitions to be processed
   *
   * Invariant: definitions that are in @c _unprocessed aren't in
   * @c _index nor @c _pred2Defs.
   */
  FormulaQueue _unprocessed;

  typedef SkipList<FormulaUnit*, UnitComparator> FormulaSkipList;

  /**
   * Contains FormulaSkipList objects on the positions corresponding
   * to predicates we need to watch, zeroes on those we don't need
   * (because they don't have any corresponding definitions).
   */
  DArray<FormulaSkipList*> _pred2Defs;
};

}

#endif // __PDMerger__

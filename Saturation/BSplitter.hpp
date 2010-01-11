/**
 * @file BSplitter.hpp
 * Defines class BSplitter for splitting with backtracking.
 */

#ifndef __BSplitter__
#define __BSplitter__

#include "../Forwards.hpp"

#include "../Lib/Allocator.hpp"
#include "../Lib/Array.hpp"
//#include "../Lib/VirtualIterator.hpp"
#include "../Lib/Stack.hpp"

namespace Saturation {

using namespace Kernel;

class BSplitter {
private:
  typedef Stack<SplitLevel> LevelStack;
  struct SplitRecord
  {
    SplitRecord(SplitLevel level, Clause* base, Clause* comp)
     : level(level), base(base), component(comp) {}

    SplitLevel level;
    Clause* base;
    Clause* component;
    LevelStack dependent;
    Stack<Clause*> children;
    Stack<Clause*> reduced;

    CLASS_NAME("BSplitter::SplitRecord");
    USE_ALLOCATOR(SplitRecord);
  };
public:
  void init(SaturationAlgorithm* sa);

  bool split(Clause* cl);

  void onClauseReduction(Clause* cl, Clause* to, Clause* premise, bool forward);
  void onNewClause(Clause* cl);

  void backtrack(ClauseIterator emptyClauses);
private:

  SplitSet* getTransitivelyDependentLevels(SplitLevel l);

  bool stackSplitting() { return false; }
  /**
   * Return true if splitting is to be performed only if both
   * resulting clauses contain less positive literals than
   * the original one.
   */
  bool splittingForHorn() { return false; }

  bool canBeSplitted(Clause* cl) { return true; }
  Clause* getComponent(Clause* icl);

  SplitSet* getNewClauseSplitSet(Clause* cl);
  void assignClauseSplitSet(Clause* cl, SplitSet* splits);

  void getAlternativeClauses(Clause* base, Clause* firstComp, Clause* refutation, ClauseStack& acc);

  SplitLevel _nextLev;
  SaturationAlgorithm* _sa;
  ZIArray<SplitRecord*> _db;
};

}

#endif // __BSplitter__

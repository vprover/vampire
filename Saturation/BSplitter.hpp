/**
 * @file BSplitter.hpp
 * Defines class BSplitter for splitting with backtracking.
 */

#ifndef __BSplitter__
#define __BSplitter__

#include "../Forwards.hpp"

#include "../Lib/Allocator.hpp"
#include "../Lib/Array.hpp"
#include "../Lib/Stack.hpp"

#include "../Kernel/Clause.hpp"
#include "../Kernel/RCClauseStack.hpp"

#include "Splitter.hpp"

namespace Saturation {

using namespace Kernel;

class BSplitter : public Splitter {
private:
  struct ReductionRecord
  {
    ReductionRecord(unsigned timestamp, Clause* clause) : timestamp(timestamp), clause(clause) {}
    unsigned timestamp;
    Clause* clause;
  };

  typedef Stack<SplitLevel> LevelStack;
  struct SplitRecord
  {
    SplitRecord(Clause* base, Clause* comp)
     : base(base), component(comp)
    {
      base->incRefCnt();
      component->incRefCnt();
    }

    ~SplitRecord()
    {
      base->decRefCnt();
      component->decRefCnt();
    }

    void addReduced(Clause* cl);

    Clause* base;
    Clause* component;
    LevelStack dependent;
    ClauseStack children;
    Stack<ReductionRecord> reduced;

    CLASS_NAME("BSplitter::SplitRecord");
    USE_ALLOCATOR(SplitRecord);
  };
public:
  BSplitter() : _nextLev(1) {}

  bool doSplitting(Clause* cl);

  void onClauseReduction(Clause* cl, Clause* premise, Clause* replacement=0);
  void onNewClause(Clause* cl);
  void onAllProcessed();

  bool handleEmptyClause(Clause* cl);

  void backtrack(ClauseIterator emptyClauses);
private:

  SplitSet* getTransitivelyDependentLevels(SplitLevel l);

  bool stackSplitting() { return false; }

  bool canBeSplitted(Clause* cl) { return true; }
  Clause* getComponent(Clause* icl);

  SplitSet* getNewClauseSplitSet(Clause* cl);
  void assignClauseSplitSet(Clause* cl, SplitSet* splits);

  void getAlternativeClauses(Clause* base, Clause* firstComp, Clause* refutation, SplitLevel refLvl,
      RCClauseStack& acc, SplitSet*& altSplitSet);

  void assertSplitLevelsExist(SplitSet* s);

  SplitLevel _nextLev;

  ZIArray<SplitRecord*> _db;
  RCClauseStack _splitRefutations;
};

}

#endif // __BSplitter__

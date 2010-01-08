/**
 * @file BSplitter.hpp
 * Defines class BSplitter for splitting with backtracking.
 */

#ifndef __BSplitter__
#define __BSplitter__

#include "../Forwards.hpp"

#include "../Lib/Array.hpp"
#include "../Lib/Stack.hpp"

namespace Saturation {

using namespace Kernel;

class BSplitter {
private:
  struct SplitRecord
  {
    SplitLevel level;
    Clause* base;
    Stack<SplitLevel> dependent;
    Stack<Clause*> alternatives;
    Stack<Clause*> children;
    Stack<Clause*> reduced;
  };
public:
  void init(SaturationAlgorithm* sa);

  bool split(Clause* cl);

  void onClauseReduction(Clause* cl, Clause* to, Clause* premise, bool forward);
  void onNewClause(Clause* cl);
private:

  bool stackSplitting() { return false; }

  bool canBeSplitted(Clause* cl) { return true; }
  bool getComponents(Clause* icl, Clause*& ocl1, Clause*& ocl2);

  SplitSet* getNewClauseSplitSet(Clause* cl);
  void backtrack(Clause* cl);

  SplitLevel _nextLev;
  SaturationAlgorithm* _sa;
  ZIArray<SplitRecord*> _db;
};

}

#endif // __BSplitter__

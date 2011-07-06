/**
 * @file HornRevealer.hpp
 * Defines class HornRevealer.
 */

#ifndef __HornRevealer__
#define __HornRevealer__

#include "Forwards.hpp"

#include "Lib/Stack.hpp"

#include "SAT/TWLSolver.hpp"


namespace Shell {

using namespace Lib;
using namespace Kernel;
using namespace SAT;

class HornRevealer {
public:
  void apply(UnitList*& inp);

private:
  void buildSatProblem(UnitList* clist);
  void discoverGoals(UnitList*& clist);
  bool isReversed(unsigned pred);
  bool isGoal(Clause* cl);
  void addToSatProblem(Clause* cl);

  unsigned pred2var(unsigned pred) { return pred+1; }

  TWLSolver _solver;
  SATClauseStack _satPrb;
};

}

#endif // __HornRevealer__

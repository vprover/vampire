/**
 * @file TabulationAlgorithm.hpp
 * Defines class TabulationAlgorithm.
 */

#ifndef __TabulationAlgorithm__
#define __TabulationAlgorithm__

#include "Forwards.hpp"

#include "Lib/ScopedPtr.hpp"
#include "Lib/SmartPtr.hpp"

#include "Kernel/MainLoop.hpp"

#include "Inferences/InferenceEngine.hpp"

#include "TabulationContainers.hpp"

namespace Tabulation {

using namespace Lib;
using namespace Kernel;
using namespace Inferences;
using namespace Shell;

class TabulationAlgorithm : public MainLoop {
public:
  TabulationAlgorithm();

  virtual void addInputClauses(ClauseIterator cit);
  virtual MainLoopResult run();

private:
  void selectGoalLiteral(Clause* cl);
  void processGoal(Clause* cl);

  Clause* generateGoal(Clause* cl, Literal* resolved, int parentGoalAge=0);

  void addGoalProducingRule(Clause* oldGoal);
  void addProducingRule(Clause* cl, Literal* head=0);
  void addGoal(Clause* cl);

  Clause* simplifyClause(Clause* cl);

  GIContainer _theoryContainer;
  GoalContainer _goalContainer;
  GoalLiteralContainer _glContainer;
  UnprocessedLemmaContainer _unprocLemmaContainer;

  ImmediateSimplificationEngineSP _ise;

  Clause* _refutation;
};

}

#endif // __TabulationAlgorithm__

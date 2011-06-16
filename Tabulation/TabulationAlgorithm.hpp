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

#include "Producer.hpp"
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

  void addGoal(Clause* cl);
  void addLemma(Clause* cl);
private:
  void selectGoalLiteral(Clause* cl);
  void processGoal(Clause* cl);

  Clause* generateGoal(Clause* cl, Literal* resolved, int parentGoalAge=0);

  void addGoalProducingRule(Clause* oldGoal);
  void addProducingRule(Clause* cl, Literal* head=0);

  Clause* simplifyClause(Clause* cl);

  GIContainer _theoryContainer;
  GoalContainer _goalContainer;
  GoalLiteralContainer _glContainer;

  ImmediateSimplificationEngineSP _ise;

  GoalProducer _gp;
  Producer _producer;

  Clause* _refutation;
};

}

#endif // __TabulationAlgorithm__

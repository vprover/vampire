/**
 * @file TabulationAlgorithm.hpp
 * Defines class TabulationAlgorithm.
 */

#ifndef __TabulationAlgorithm__
#define __TabulationAlgorithm__

#include <utility>

#include "Forwards.hpp"

#include "Lib/DHSet.hpp"
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

  void addGoal(Clause* cl);
  void addLemma(Clause* cl);
private:
  friend class Producer;
  friend class GoalProducer;

  virtual MainLoopResult runImpl();

  void selectGoalLiteral(Clause*& cl);
  void processGoal(Clause* cl);

  Clause* processSubsumedGoalLiterals(Clause* goal);

  Clause* generateGoal(Clause* cl, Literal* resolved, int parentGoalAge=0, ResultSubstitution* subst=0, bool result=false);

  void addGoalProducingRule(Clause* oldGoal);
  void addProducingRule(Clause* cl, Literal* head=0);

  Clause* simplifyClause(Clause* cl);
  static Clause* removeDuplicateLiterals(Clause* cl);

  typedef pair<Clause*, Literal*> RuleSpec;
  DHSet<RuleSpec> _addedProducingRules;

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

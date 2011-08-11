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
  TabulationAlgorithm(Problem& prb, const Options& opt);


  LiteralIndexingStructure& getLemmaIndex() { return _gp.getLemmaIndex(); }

  void addGoal(Clause* cl);
  void addLemma(Clause* cl);

protected:
  virtual void init();
  virtual MainLoopResult runImpl();

private:
  friend class Producer;
  friend class GoalProducer;


  void selectGoalLiteral(Clause*& cl);
  void processGoal(Clause* cl);

  Clause* processSubsumedGoalLiterals(Clause* goal);

  Clause* generateGoal(Clause* cl, Literal* resolved, int parentGoalAge=0, ResultSubstitution* subst=0, bool result=false);

  void addGoalProducingRule(Clause* oldGoal);
  void addProducingRule(Clause* cl, Literal* head=0, ResultSubstitution* subst=0, bool result=false);

  Clause* simplifyInputClause(Clause* cl);
  static Clause* removeDuplicateLiterals(Clause* cl);
  static bool isSimpleTautology(Clause* cl);

  typedef pair<Clause*, Literal*> RuleSpec;
  DHSet<RuleSpec> _addedProducingRules;

  GIContainer _theoryContainer;
  GoalContainer _goalContainer;
  GoalLiteralContainer _glContainer;

  ScopedPtr<ImmediateSimplificationEngine> _ise;

  GoalProducer _gp;
  Producer _producer;

  Clause* _refutation;

  bool _instatiateProducingRules;
};

}

#endif // __TabulationAlgorithm__

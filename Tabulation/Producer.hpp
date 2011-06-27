/**
 * @file Producer.hpp
 * Defines class Producer.
 */

#ifndef __Producer__
#define __Producer__

#include "Forwards.hpp"

#include "Lib/Deque.hpp"
#include "Lib/ScopedPtr.hpp"
#include "Lib/Stack.hpp"

#include "Indexing/LiteralIndex.hpp"
#include "Indexing/LiteralSubstitutionTree.hpp"

#include "Inferences/URResolution.hpp"
#include "Inferences/SLQueryBackwardSubsumption.hpp"

#include "Saturation/ClauseContainer.hpp"

#include "TabulationContainers.hpp"

namespace Tabulation {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Inferences;
using namespace Saturation;

class Producer {
public:
  Producer(TabulationAlgorithm& alg);

  void addRule(Clause* rule);
  void removeRule(Clause* rule);
  void onLemma(Clause* lemma);
  void removeLemma(Clause* lemma);

  bool hasLemma() { return !_unprocLemmaCont.isEmpty(); }
  void processLemma();

  bool subsumedByLemma(Literal* lit);

  /** To be called form the top level of the loop */
  void onSafePoint();


  bool isRuleForwardSubsumed(Clause* rule);
  bool isRuleSubsumedBy(Clause* queryRule, Clause* subsumingRule);

  void performRuleBackwardSubsumption(Clause* rule);

  Clause* performLemmaSubsumptionResolution(Clause* tgtRule, Clause* lemma);
  void doBackwardLemmaSubsumptionResolution(Clause* lemma);
  Clause* doForwardLemmaSubsumptionResolution(Clause* rule);
private:

  void performRuleAddition(Clause* rule);
  void performRuleRemoval(Clause* rule);

  void performURR(Clause* cl);

  void newLemma(Clause* lemma);

  typedef AWClauseContainer UnprocessedLemmaContainer;

  class ActiveContainer : public ClauseContainer {
  public:
    virtual void add(Clause* c);
    virtual void remove(Clause* c);
  };

  DHSet<Clause*> _toRemove;

  ClauseStack _rulesToRemove;
  ClauseStack _lemmasToRemove;
  Deque<Clause*> _rulesToAdd;
  Deque<Clause*> _lemmasToAdd;

  UnprocessedLemmaContainer _unprocLemmaCont;

  /** Container for active lemmas and rules */
  ActiveContainer _activeCont;

  ScopedPtr<UnitClauseLiteralIndex> _unprocLemmaIndex;
  ScopedPtr<UnitClauseLiteralIndex> _lemmaIndex;
  ScopedPtr<NonUnitClauseLiteralIndex> _ruleTailIndex;

  ScopedPtr<LiteralSubstitutionTree> _ruleHeadIndex;

  ScopedPtr<ClauseSubsumptionIndex> _ruleSubsumptionIndex;
  ScopedPtr<SimplifyingLiteralIndex> _ruleBwSubsumptionIndex;

  ScopedPtr<SLQueryBackwardSubsumption> _bwSubsumptionRule;

  ScopedPtr<URResolution> _urr;
  TabulationAlgorithm& _alg;
};

}

#endif // __Producer__

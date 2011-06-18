/**
 * @file Producer.hpp
 * Defines class Producer.
 */

#ifndef __Producer__
#define __Producer__

#include "Forwards.hpp"

#include "Lib/ScopedPtr.hpp"

#include "Indexing/LiteralIndex.hpp"
#include "Indexing/LiteralSubstitutionTree.hpp"

#include "Inferences/URResolution.hpp"

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

  bool hasLemma() { return !_unprocLemmaCont.isEmpty(); }
  void processLemma();

  bool subsumedByLemma(Literal* lit);

  /** To be called form the top level of the loop */
  void onSafePoint();

private:

  void performURR(Clause* cl);

  typedef AWClauseContainer UnprocessedLemmaContainer;

  class ActiveContainer : public ClauseContainer {
  public:
    virtual void add(Clause* c);
    virtual void remove(Clause* c);
  };

  ClauseStack _rulesToRemove;

  UnprocessedLemmaContainer _unprocLemmaCont;

  /** Container for active lemmas and rules */
  ActiveContainer _activeCont;

  ScopedPtr<UnitClauseLiteralIndex> _unprocLemmaIndex;
  ScopedPtr<UnitClauseLiteralIndex> _lemmaIndex;
  ScopedPtr<NonUnitClauseLiteralIndex> _ruleIndex;

  ScopedPtr<LiteralSubstitutionTree> _ruleHeadIndex;

  ScopedPtr<URResolution> _urr;
  TabulationAlgorithm& _alg;
};

}

#endif // __Producer__

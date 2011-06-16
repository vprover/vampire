/**
 * @file Producer.hpp
 * Defines class Producer.
 */

#ifndef __Producer__
#define __Producer__

#include "Forwards.hpp"

#include "Lib/ScopedPtr.hpp"

#include "Indexing/LiteralIndex.hpp"

#include "Inferences/URResolution.hpp"

#include "Saturation/AWPassiveClauseContainer.hpp"
#include "Saturation/ClauseContainer.hpp"

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
  void onLemma(Clause* lemma);

  bool hasLemma() { return !_unprocLemmaCont.isEmpty(); }
  void processLemma();

private:

  void performURR(Clause* cl);

  typedef AWPassiveClauseContainer UnprocessedLemmaContainer;

  class LemmaContainer : public ClauseContainer {
  public:
    virtual void add(Clause* c);
  };

  typedef LemmaContainer RuleContainer;

  UnprocessedLemmaContainer _unprocLemmaCont;
  LemmaContainer _lemmaCont;
  RuleContainer _ruleCont;
  ScopedPtr<UnitClauseLiteralIndex> _lemmaIndex;
  ScopedPtr<NonUnitClauseLiteralIndex> _ruleIndex;
  ScopedPtr<URResolution> _urr;
  TabulationAlgorithm& _alg;
};

}

#endif // __Producer__

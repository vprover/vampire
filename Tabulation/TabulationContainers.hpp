/**
 * @file TabulationContainers.hpp
 * Defines classes for tabulation containers.
 */

#ifndef __TabulationContainers__
#define __TabulationContainers__

#include "Forwards.hpp"

#include "Lib/MapToLIFO.hpp"
#include "Lib/ScopedPtr.hpp"

#include "Indexing/LiteralIndex.hpp"
#include "Indexing/LiteralIndexingStructure.hpp"


#include "Saturation/ClauseContainer.hpp"
#include "Saturation/AWPassiveClauseContainer.hpp"

namespace Tabulation {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Inferences;
using namespace Saturation;

/**
 * Container indexed with generating literal index that indexes
 * all selected literals.
 */
class GIContainer : public ClauseContainer {
public:
  GIContainer();

  virtual void add(Clause* c);

  GeneratingLiteralIndex* getIndex() { return _unifIndex.ptr(); }
private:
  ScopedPtr<GeneratingLiteralIndex> _unifIndex;
};

typedef AWClauseContainer GoalContainer;

class GoalLiteralContainer
{
public:
  GoalLiteralContainer();

  void add(Literal* lit);
  bool isSubsumed(Literal* lit);
private:
  ScopedPtr<LiteralIndexingStructure> _index;
};

class GoalProducer
{
public:
  GoalProducer(TabulationAlgorithm& alg);

  void addRule(Clause* goal, Literal* activator);

  void onLemma(Clause* lemma);

  LiteralIndexingStructure& getLemmaIndex() { return *_lemmaIndex; }

  static Clause* makeInstance(Clause* resCl, ResultSubstitution& subst, bool clIsResult);
private:


  ScopedPtr<LiteralIndexingStructure> _lemmaIndex;
  ScopedPtr<LiteralIndexingStructure> _activatorIndex;

  TabulationAlgorithm& _alg;
};

}

#endif // __TabulationContainers__

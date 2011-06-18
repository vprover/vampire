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

class AWClauseContainer: public ClauseContainer
{
public:
  AWClauseContainer();

  void add(Clause* cl);
  void remove(Clause* cl);

  /**
   * Set age-weight ratio
   * @since 08/01/2008 flight Murcia-Manchester
   */
  void setAgeWeightRatio(int age,int weight)
  {
    ASS(age >= 0);
    ASS(weight >= 0);
    ASS(age > 0 || weight > 0);

    _ageRatio = age;
    _weightRatio = weight;
  }

  Clause* popSelected();
  /** True if there are no passive clauses */
  bool isEmpty() const
  { return _ageQueue.isEmpty() && _weightQueue.isEmpty(); }

  unsigned size() const { return _size; }

  static Comparison compareWeight(Clause* cl1, Clause* cl2);

private:
  /** The age queue, empty if _ageRatio=0 */
  AgeQueue _ageQueue;
  /** The weight queue, empty if _weightRatio=0 */
  WeightQueue _weightQueue;
  /** the age ratio */
  int _ageRatio;
  /** the weight ratio */
  int _weightRatio;
  /** current balance. If &lt;0 then selection by age, if &gt;0
   * then by weight */
  int _balance;

  unsigned _size;
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
private:

  static Clause* makeInstance(Clause* resCl, ResultSubstitution& subst, bool clIsResult);

  ScopedPtr<LiteralIndexingStructure> _lemmaIndex;
  ScopedPtr<LiteralIndexingStructure> _activatorIndex;

  TabulationAlgorithm& _alg;
};

}

#endif // __TabulationContainers__

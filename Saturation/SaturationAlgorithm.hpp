/**
 * @file SaturationAlgorithm.hpp
 * Defines class SaturationAlgorithm
 *
 */

#ifndef __SaturationAlgorithm__
#define __SaturationAlgorithm__

#include "../Forwards.hpp"

#include "../Kernel/Clause.hpp"
#include "../Lib/List.hpp"
#include "../Lib/Event.hpp"
#include "../Indexing/IndexManager.hpp"
#include "../Inferences/InferenceEngine.hpp"

#include "Limits.hpp"
#include "SaturationResult.hpp"

#if VDEBUG
#include<iostream>
#endif

namespace Saturation
{

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Inferences;

class SaturationAlgorithm
{
public:
  SaturationAlgorithm(PassiveClauseContainerSP passiveContainer, LiteralSelectorSP selector);
  virtual ~SaturationAlgorithm();

  void setGeneratingInferenceEngine(GeneratingInferenceEngineSP generator);
  void setImmediateSimplificationEngine(ImmediateSimplificationEngineSP immediateSimplifier);

  void addForwardSimplifierToFront(ForwardSimplificationEngineSP fwSimplifier);
  void addBackwardSimplifierToFront(BackwardSimplificationEngineSP bwSimplifier);

  virtual SaturationResult saturate() = 0;

  void addInputClauses(ClauseIterator cit);

  virtual ClauseContainer* getSimplificationClauseContainer() = 0;
  virtual ClauseContainer* getGenerationClauseContainer() = 0;

  Limits* getLimits() { return &_limits; }
  IndexManager* getIndexManager() { return &_imgr; }

  static SaturationAlgorithmSP createFromOptions();

protected:
  void addUnprocessedClause(Clause* cl);

  bool isRefutation(Clause* c);
  bool forwardSimplify(Clause* c);
  void backwardSimplify(Clause* c);
  void activate(Clause* c);

#if VDEBUG
  void onActiveAdded(Clause* c)
  {
    cout<<"## Active added: "<<(*c)<<endl;
  }
  void onPassiveAdded(Clause* c)
  {
    cout<<"# Passive added: "<<(*c)<<endl;
  }
  void onPassiveRemoved(Clause* c)
  {
    cout<<"Passive removed: "<<(*c)<<endl;
  }
  void onUnprocessedAdded(Clause* c)
  {
    cout<<"++ Unprocessed added: "<<(*c)<<endl;
  }
  void onUnprocessedRemoved(Clause* c)
  {
    cout<<"Unprocessed removed: "<<(*c)<<endl;
  }
  void onUnprocessedSelected(Clause* c)
  {
    cout<<"-- Unprocessed selected: "<<(*c)<<endl;
  }
#endif


private:
  Limits _limits;
  IndexManager _imgr;
protected:
  UnprocessedClauseContainer* _unprocessed;
  PassiveClauseContainerSP _passive;
  ActiveClauseContainer* _active;

  GeneratingInferenceEngineSP _generator;
  ImmediateSimplificationEngineSP _immediateSimplifier;

  typedef List<ForwardSimplificationEngineSP> FwSimplList;
  FwSimplList* _fwSimplifiers;

  typedef List<BackwardSimplificationEngineSP> BwSimplList;
  BwSimplList* _bwSimplifiers;

  LiteralSelectorSP _selector;
};


};

#endif /*__SaturationAlgorithm__*/

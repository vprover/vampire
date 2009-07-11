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
#include "Splitter.hpp"

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


  void setFwDemodulator(ForwardSimplificationEngineSP fwDemodulator);
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
  virtual void addInputSOSClause(Clause* cl);

  void addUnprocessedClause(Clause* cl);

  bool isRefutation(Clause* c);
  bool forwardSimplify(Clause* c);
  void backwardSimplify(Clause* c);
  void addToPassive(Clause* c);
  void reanimate(Clause* c);
  void activate(Clause* c);

  void onActiveAddedReport(Clause* c);
  void onActiveRemovedReport(Clause* c);
  void onPassiveAddedReport(Clause* c);
  void onPassiveRemovedReport(Clause* c);
  void onPassiveSelectedReport(Clause* c);
  void onUnprocessedAddedReport(Clause* c);
  void onUnprocessedRemovedReport(Clause* c);
  void onUnprocessedSelectedReport(Clause* c);

  void handleSaturationStart();
  int elapsedTime();


  virtual void onActiveRemoved(Clause* cl);
  virtual void onPassiveRemoved(Clause* cl);

private:
  void passiveRemovedHandler(Clause* cl);
  void activeRemovedHandler(Clause* cl);

  void addInputClause(Clause* cl);
  void addUnprocessedFinalClause(Clause* cl);

  Limits _limits;
  IndexManager _imgr;
protected:

  int _startTime;
  bool _performSplitting;
  bool _someSplitting;

  UnprocessedClauseContainer* _unprocessed;
  PassiveClauseContainerSP _passive;
  ActiveClauseContainer* _active;

  GeneratingInferenceEngineSP _generator;
  ImmediateSimplificationEngineSP _immediateSimplifier;

  typedef List<ForwardSimplificationEngineSP> FwSimplList;
  FwSimplList* _fwSimplifiers;
  ForwardSimplificationEngineSP _fwDemodulator;

  typedef List<BackwardSimplificationEngineSP> BwSimplList;
  BwSimplList* _bwSimplifiers;

  LiteralSelectorSP _selector;

  Splitter _splitter;

  SubscriptionData _passiveContRemovalSData;
  SubscriptionData _activeContRemovalSData;
};


};

#endif /*__SaturationAlgorithm__*/

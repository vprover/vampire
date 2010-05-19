/**
 * @file SaturationAlgorithm.hpp
 * Defines class SaturationAlgorithm
 *
 */

#ifndef __SaturationAlgorithm__
#define __SaturationAlgorithm__

#include "../Forwards.hpp"

#include "../Kernel/Clause.hpp"
#include "../Kernel/RCClauseStack.hpp"

#include "../Lib/DHMap.hpp"
#include "../Lib/Event.hpp"
#include "../Lib/List.hpp"

#include "../Indexing/ClauseSharing.hpp"
#include "../Indexing/IndexManager.hpp"

#include "../Inferences/InferenceEngine.hpp"
#include "../Inferences/PropositionalToBDDISE.hpp"

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
  SaturationAlgorithm(PassiveClauseContainer* passiveContainer, LiteralSelector* selector);
  virtual ~SaturationAlgorithm();

  void setGeneratingInferenceEngine(GeneratingInferenceEngineSP generator);
  void setImmediateSimplificationEngine(ImmediateSimplificationEngineSP immediateSimplifier);


  void addForwardSimplifierToFront(ForwardSimplificationEngineSP fwSimplifier);
  void addBackwardSimplifierToFront(BackwardSimplificationEngineSP bwSimplifier);

  SaturationResult saturate();

  void addInputClauses(ClauseIterator cit);

  void addNewClause(Clause* cl);
  bool clausesFlushed();

  void removeActiveOrPassiveClause(Clause* cl);

  void onClauseReduction(Clause* cl, Clause* replacement, Clause* premise,
      Clause* reductionPremise=0, bool forward=true);
  void onClauseReduction(Clause* cl, Clause* replacement, ClauseIterator premises,
      bool forward=true);
  void onNonRedundantClause(Clause* c);
  void onParenthood(Clause* cl, Clause* parent);

  virtual ClauseContainer* getSimplificationClauseContainer() = 0;
  virtual ClauseContainer* getGenerationClauseContainer() = 0;

  ClauseIterator activeClauses();
  ClauseIterator passiveClauses();
  size_t activeClauseCount();
  size_t passiveClauseCount();

  Limits* getLimits() { return &_limits; }
  IndexManager* getIndexManager() { return &_imgr; }
  ClauseSharing* getSharing() { return &_sharing; }

  static SaturationAlgorithmSP createFromOptions();

protected:
  void doUnprocessedLoop();
  virtual void handleUnsuccessfulActivation(Clause* c);

  virtual bool handleClauseBeforeActivation(Clause* c);

  void addInputSOSClause(Clause* cl);

  void newClausesToUnprocessed();

  void addUnprocessedClause(Clause* cl);

  static bool isRefutation(Clause* c);
  bool forwardSimplify(Clause* c);
  void backwardSimplify(Clause* c);
  void addToPassive(Clause* c);
  void reanimate(Clause* c);
  bool activate(Clause* c);

  virtual void onSOSClauseAdded(Clause* c) {}
  void onActiveAdded(Clause* c);
  virtual void onActiveRemoved(Clause* c);
  virtual void onPassiveAdded(Clause* c);
  virtual void onPassiveRemoved(Clause* c);
  void onPassiveSelected(Clause* c);
  void onUnprocessedAdded(Clause* c);
  void onUnprocessedRemoved(Clause* c);
  virtual void onUnprocessedSelected(Clause* c);
  void onNewClause(Clause* c);
  void onNewUsefulPropositionalClause(Clause* c);

  virtual void onClauseRetained(Clause* cl);

  void onAllProcessed();

  int elapsedTime();

  virtual bool isComplete();

  struct RefutationFoundException;

private:
  void passiveRemovedHandler(Clause* cl);
  void activeRemovedHandler(Clause* cl);

  void addInputClause(Clause* cl);

  void handleEmptyClause(Clause* cl);
  void performEmptyClauseParentSubsumption(Clause* cl, BDDNode* emptyClauseProp);

  Clause* doImmediateSimplification(Clause* cl);

  Limits _limits;
  IndexManager _imgr;

  class TotalSimplificationPerformer;
  class PartialSimplificationPerformer;
protected:

  int _startTime;
  bool _propToBDD;
  bool _clauseActivationInProgress;

  RCClauseStack _newClauses;

  ClauseStack _postponedClauseRemovals;

  UnprocessedClauseContainer* _unprocessed;
  PassiveClauseContainer* _passive;
  ActiveClauseContainer* _active;

  GeneratingInferenceEngineSP _generator;
  ImmediateSimplificationEngineSP _immediateSimplifier;

  typedef List<ForwardSimplificationEngineSP> FwSimplList;
  FwSimplList* _fwSimplifiers;

  typedef List<BackwardSimplificationEngineSP> BwSimplList;
  BwSimplList* _bwSimplifiers;

  LiteralSelector* _selector;

  Splitter* _splitter;

  PropositionalToBDDISE _propToBDDConv;

  ConsequenceFinder* _consFinder;
  SymElOutput* _symEl;

  BDDMarkingSubsumption* _bddMarkingSubsumption;

  /** Index that takes care of the sharing and merging of clauses */
  ClauseSharing _sharing;

  SubscriptionData _passiveContRemovalSData;
  SubscriptionData _activeContRemovalSData;
};


};

#endif /*__SaturationAlgorithm__*/

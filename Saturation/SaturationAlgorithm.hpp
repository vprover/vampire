/**
 * @file SaturationAlgorithm.hpp
 * Defines class SaturationAlgorithm
 *
 */

#ifndef __SaturationAlgorithm__
#define __SaturationAlgorithm__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/Event.hpp"
#include "Lib/List.hpp"
#include "Lib/ScopedPtr.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/MainLoop.hpp"
#include "Kernel/RCClauseStack.hpp"

#include "Indexing/ClauseSharing.hpp"
#include "Indexing/IndexManager.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Inferences/PropositionalToBDDISE.hpp"

#include "Limits.hpp"

#if VDEBUG
#include<iostream>
#endif

namespace Saturation
{

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Inferences;

class SaturationAlgorithm : public MainLoop
{
public:
  static SaturationAlgorithm* createFromOptions(Problem& prb, const Options& opt, IndexManager* indexMgr=0);

  SaturationAlgorithm(Problem& prb, const Options& opt);
  virtual ~SaturationAlgorithm();


  //the following two functions allow to run the saturation algorithm step by step.
  void initAlgorithmRun();
  void doOneAlgorithmStep();

  void setGeneratingInferenceEngine(GeneratingInferenceEngine* generator);
  void setImmediateSimplificationEngine(ImmediateSimplificationEngine* immediateSimplifier);


  void addForwardSimplifierToFront(ForwardSimplificationEngine* fwSimplifier);
  void addBackwardSimplifierToFront(BackwardSimplificationEngine* bwSimplifier);


  void addNewClause(Clause* cl);
  bool clausesFlushed();

  void removeActiveOrPassiveClause(Clause* cl);

  void onClauseReduction(Clause* cl, Clause* replacement, Clause* premise,
      Clause* reductionPremise=0, bool forward=true);
  void onClauseReduction(Clause* cl, Clause* replacement, ClauseIterator premises,
      bool forward=true);
  void onNonRedundantClause(Clause* c);
  void onParenthood(Clause* cl, Clause* parent);

  virtual ClauseContainer* getSimplifyingClauseContainer() = 0;
  virtual ClauseContainer* getGeneratingClauseContainer() { return _active; }

  ClauseIterator activeClauses();
  ClauseIterator passiveClauses();
  size_t activeClauseCount();
  size_t passiveClauseCount();

  Limits* getLimits() { return &_limits; }
  IndexManager* getIndexManager() { return _imgr.ptr(); }
  ClauseSharing* getSharing() { return &_sharing; }
  AnswerLiteralManager* getAnswerLiteralManager() { return _answerLiteralManager; }
  Ordering& getOrdering() const { return *_ordering; }
  LiteralSelector& getLiteralSelector() const { return *_selector; }

  /**
   * if an intermediate clause is derived somewhere, it still needs to be passed to this function
   */
  void onNewClause(Clause* c);


  /**
   * If the saturation algorithm run is in progress, return pointer
   * to the object; otherwise return zero.
   */
  static SaturationAlgorithm* tryGetInstance() { return s_instance; }

  static void tryUpdateFinalClauseCount();

protected:

  virtual void init();
  virtual MainLoopResult runImpl();

  void doUnprocessedLoop();
  virtual void handleUnsuccessfulActivation(Clause* c);

  virtual bool handleClauseBeforeActivation(Clause* c);

  void addInputSOSClause(Clause* cl);

  void newClausesToUnprocessed();

  void addUnprocessedClause(Clause* cl);

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
  void onNewUsefulPropositionalClause(Clause* c);

  virtual void onClauseRetained(Clause* cl);

  void onAllProcessed();

  int elapsedTime();

  virtual bool isComplete();

private:
  void passiveRemovedHandler(Clause* cl);
  void activeRemovedHandler(Clause* cl);

  void addInputClause(Clause* cl);

  LiteralSelector& getSosLiteralSelector();

  void handleEmptyClause(Clause* cl);
  void performEmptyClauseParentSubsumption(Clause* cl, BDDNode* emptyClauseProp);

  Clause* doImmediateSimplification(Clause* cl);

  MainLoopResult saturateImpl();

  Limits _limits;
  SmartPtr<IndexManager> _imgr;

  class TotalSimplificationPerformer;
  class PartialSimplificationPerformer;

  static SaturationAlgorithm* s_instance;
protected:

  bool _completeOptionSettings;
  int _startTime;
  bool _propToBDD;
  bool _clauseActivationInProgress;

  RCClauseStack _newClauses;

  ClauseStack _postponedClauseRemovals;

  UnprocessedClauseContainer* _unprocessed;
  PassiveClauseContainer* _passive;
  ActiveClauseContainer* _active;

  ScopedPtr<GeneratingInferenceEngine> _generator;
  ScopedPtr<ImmediateSimplificationEngine> _immediateSimplifier;

  typedef List<ForwardSimplificationEngine*> FwSimplList;
  FwSimplList* _fwSimplifiers;

  typedef List<BackwardSimplificationEngine*> BwSimplList;
  BwSimplList* _bwSimplifiers;

  OrderingSP _ordering;
  ScopedPtr<LiteralSelector> _selector;

  Splitter* _splitter;

  PropositionalToBDDISE _propToBDDConv;

  ConsequenceFinder* _consFinder;
  SymElOutput* _symEl;

  BDDMarkingSubsumption* _bddMarkingSubsumption;

  AnswerLiteralManager* _answerLiteralManager;

  /** Index that takes care of the sharing and merging of clauses */
  ClauseSharing _sharing;

  SubscriptionData _passiveContRemovalSData;
  SubscriptionData _activeContRemovalSData;

  /**
   * Literal selector for set-of-support.
   *
   * This variable is initialized and used only by the
   * @c getSosLiteralSelector() function
   */
  ScopedPtr<LiteralSelector> _sosLiteralSelector;
};


};

#endif /*__SaturationAlgorithm__*/

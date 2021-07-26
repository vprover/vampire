/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
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

#include "Indexing/IndexManager.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Inferences/Instantiation.hpp"
#include "Inferences/TheoryInstAndSimp.hpp"

#include "Saturation/ExtensionalityClauseContainer.hpp"

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
  CLASS_NAME(SaturationAlgorithm);
  USE_ALLOCATOR(SaturationAlgorithm);

  static SaturationAlgorithm* createFromOptions(Problem& prb, const Options& opt, IndexManager* indexMgr=0);

  SaturationAlgorithm(Problem& prb, const Options& opt);
  virtual ~SaturationAlgorithm();


  //the following two functions allow to run the saturation algorithm step by step.
  void initAlgorithmRun();
  void doOneAlgorithmStep();

  UnitList* collectSaturatedSet();

  void setGeneratingInferenceEngine(SimplifyingGeneratingInference* generator);
  void setImmediateSimplificationEngine(ImmediateSimplificationEngine* immediateSimplifier);

  void setLabelFinder(LabelFinder* finder){ _labelFinder = finder; }

  void addForwardSimplifierToFront(ForwardSimplificationEngine* fwSimplifier);
  void addSimplifierToFront(SimplificationEngine* simplifier);
  void addBackwardSimplifierToFront(BackwardSimplificationEngine* bwSimplifier);


  void addNewClause(Clause* cl);
  bool clausesFlushed();

  void removeActiveOrPassiveClause(Clause* cl);

  //Run when clause cl has been simplified. Replacement is the array of replacing
  //clauses which can be empty
  void onClauseReduction(Clause* cl, Clause** replacements, unsigned numOfReplacements, 
                         Clause* premise, bool forward=true);
  void onClauseReduction(Clause* cl, Clause** replacements, unsigned numOfReplacements, 
                         ClauseIterator premises,
      bool forward=true);
  void onNonRedundantClause(Clause* c);
  void onParenthood(Clause* cl, Clause* parent);

  virtual ClauseContainer* getSimplifyingClauseContainer() = 0;
  virtual ClauseContainer* getGeneratingClauseContainer() { return _active; }
  ExtensionalityClauseContainer* getExtensionalityClauseContainer() {
    return _extensionality;
  }

  ClauseIterator activeClauses();

  PassiveClauseContainer* getPassiveClauseContainer() { return _passive.get(); }
  IndexManager* getIndexManager() { return _imgr.ptr(); }
  AnswerLiteralManager* getAnswerLiteralManager() { return _answerLiteralManager; }
  Ordering& getOrdering() const {  return *_ordering; }
  LiteralSelector& getLiteralSelector() const { return *_selector; }

  /** Return the number of clauses that entered the passive container */
  unsigned getGeneratedClauseCount() { return _generatedClauseCount; }

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

  Splitter* getSplitter() { return _splitter; }

protected:
  virtual void init();
  virtual MainLoopResult runImpl();
  void doUnprocessedLoop();
  virtual bool handleClauseBeforeActivation(Clause* c);
  void addInputSOSClause(Clause* cl);

  void newClausesToUnprocessed();
  void addUnprocessedClause(Clause* cl);
  bool forwardSimplify(Clause* c);
  void backwardSimplify(Clause* c);
  void addToPassive(Clause* c);
  void activate(Clause* c);
  void removeSelected(Clause*);
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
  /** called before the selected clause is deleted from the searchspace */
  virtual void beforeSelectedRemoved(Clause* cl) {};
  void onAllProcessed();
  int elapsedTime();
  virtual bool isComplete();

private:
  void passiveRemovedHandler(Clause* cl);
  void activeRemovedHandler(Clause* cl);
  void addInputClause(Clause* cl);

  LiteralSelector& getSosLiteralSelector();

  void handleEmptyClause(Clause* cl);
  Clause* doImmediateSimplification(Clause* cl);
  MainLoopResult saturateImpl();
  SmartPtr<IndexManager> _imgr;

  class TotalSimplificationPerformer;
  class PartialSimplificationPerformer;

  static SaturationAlgorithm* s_instance;
protected:

  bool _completeOptionSettings;
  int _startTime;
  bool _clauseActivationInProgress;

  RCClauseStack _newClauses;

  ClauseStack _postponedClauseRemovals;

  UnprocessedClauseContainer* _unprocessed;
  std::unique_ptr<PassiveClauseContainer> _passive;
  ActiveClauseContainer* _active;
  ExtensionalityClauseContainer* _extensionality;

  ScopedPtr<SimplifyingGeneratingInference> _generator;
  ScopedPtr<ImmediateSimplificationEngine> _immediateSimplifier;

  typedef List<ForwardSimplificationEngine*> FwSimplList;
  FwSimplList* _fwSimplifiers;

  //Simplification occurs at the same point in the loop
  //as forward and backward simplification, but does not involve
  //clauses in active. At the moment, the only simplification inference
  //is the higher-order cnfOnTheFly
  typedef List<SimplificationEngine*> SimplList;
  SimplList* _simplifiers;

  typedef List<BackwardSimplificationEngine*> BwSimplList;
  BwSimplList* _bwSimplifiers;

  OrderingSP _ordering;
  ScopedPtr<LiteralSelector> _selector;

  Splitter* _splitter;

  ConsequenceFinder* _consFinder;
  LabelFinder* _labelFinder;
  SymElOutput* _symEl;
  AnswerLiteralManager* _answerLiteralManager;
  Instantiation* _instantiation;


  SubscriptionData _passiveContRemovalSData;
  SubscriptionData _activeContRemovalSData;

  /**
   * Literal selector for set-of-support.
   *
   * This variable is initialized and used only by the
   * @c getSosLiteralSelector() function
   */
  ScopedPtr<LiteralSelector> _sosLiteralSelector;


  // counters

  /** Number of clauses that entered the unprocessed container */
  unsigned _generatedClauseCount;

  unsigned _activationLimit;
private:
  static ImmediateSimplificationEngine* createISE(Problem& prb, const Options& opt, Ordering& ordering);
};


};

#endif /*__SaturationAlgorithm__*/

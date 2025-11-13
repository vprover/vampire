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

#include "Lib/Event.hpp"
#include "Lib/List.hpp"
#include "Lib/ScopedPtr.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/MainLoop.hpp"
#include "Kernel/RCClauseStack.hpp"

#include "Indexing/IndexManager.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Inferences/Instantiation.hpp"

#include "Saturation/ExtensionalityClauseContainer.hpp"

namespace Shell { class AnswerLiteralManager; }

namespace Saturation
{

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Inferences;
using namespace Shell;

class ConsequenceFinder;
class LabelFinder;
class SymElOutput;
class Splitter;

class SaturationAlgorithm : public MainLoop
{
public:
  /**
   * Sometimes the problem does not have equality after preprocessing,
   * but still needs to be treated equationally during saturation (think theory reasoning);
   * this helper function is here to capture such cases.
  */
  static bool couldEqualityArise(const Problem& prb, const Options& opt) {
    // TODO: similar cases of "we might need equational reasoning later" might be relevant to theory reasoning too
    return prb.hasEquality() || (prb.hasFOOL() && opt.FOOLParamodulation()) ||
      (opt.questionAnswering() == Options::QuestionAnsweringMode::SYNTHESIS);
  }
  static SaturationAlgorithm* createFromOptions(Problem& prb, const Options& opt, IndexManager* indexMgr=0);

  SaturationAlgorithm(Problem& prb, const Options& opt);
  ~SaturationAlgorithm() override;


  //the following two functions allow to run the saturation algorithm step by step.
  void initAlgorithmRun();
  void doOneAlgorithmStep();

  UnitList* collectSaturatedSet();

  void setGeneratingInferenceEngine(SimplifyingGeneratingInference* generator);
  void setImmediateSimplificationEngine(ImmediateSimplificationEngine* immediateSimplifier);
  void setImmediateSimplificationEngineMany(CompositeISEMany ise) { _immediateSimplifierMany = std::move(ise); }

  void setLabelFinder(LabelFinder* finder){ _labelFinder = finder; }

  void addForwardSimplifierToFront(ForwardSimplificationEngine* fwSimplifier);
  void addExpensiveForwardSimplifierToFront(ForwardSimplificationEngine* fwSimplifier);
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

  ActiveClauseContainer* getActiveClauseContainer() { return _active; }
  PassiveClauseContainer* getPassiveClauseContainer() { return _passive.get(); }
  IndexManager* getIndexManager() { return _imgr.ptr(); }
  Ordering& getOrdering() const {  return *_ordering; }
  LiteralSelector& getLiteralSelector() const { return *_selector; }
  const PartialRedundancyHandler& parRedHandler() const { return *_partialRedundancyHandler; }

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
  FunctionDefinitionHandler& getFunctionDefinitionHandler() const { return _fnDefHandler; }

  // set a "soft" time limit to be checked periodically
  // separate to, and not as carefully checked as, Lib::Timer
  // used by FMB's FunctionRelationshipInference
  void setSoftTimeLimit(unsigned deciseconds) { _softTimeLimit = deciseconds; }

protected:
  void init() override;
  MainLoopResult runImpl() override;
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
  void onNewUsefulPropositionalClause(Clause* c);
  virtual void onClauseRetained(Clause* cl);
  /** called before the selected clause is deleted from the searchspace */
  virtual void beforeSelectedRemoved(Clause* cl) {};
  void onAllProcessed();
  virtual bool isComplete();
  virtual void poppedFromUnprocessed(Clause* cl) {}; // mainly for LRS to inherit and update its estimates there

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
  bool _clauseActivationInProgress;

  RCClauseStack _newClauses;

  ClauseStack _postponedClauseRemovals;

  UnprocessedClauseContainer* _unprocessed;
  std::unique_ptr<PassiveClauseContainer> _passive;
  ActiveClauseContainer* _active;
  ExtensionalityClauseContainer* _extensionality;

  ScopedPtr<SimplifyingGeneratingInference> _generator;
  ScopedPtr<ImmediateSimplificationEngine> _immediateSimplifier;
  CompositeISEMany _immediateSimplifierMany;

  typedef List<ForwardSimplificationEngine*> FwSimplList;
  FwSimplList* _fwSimplifiers;
  FwSimplList* _expensiveFwSimplifiers;

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
  FunctionDefinitionHandler& _fnDefHandler;
  std::unique_ptr<PartialRedundancyHandler> _partialRedundancyHandler;

  SubscriptionData _passiveContRemovalSData;
  SubscriptionData _activeContRemovalSData;

  /**
   * Literal selector for set-of-support.
   *
   * This variable is initialized and used only by the
   * @c getSosLiteralSelector() function
   */
  ScopedPtr<LiteralSelector> _sosLiteralSelector;

  // start for the first activation, for the LRS estimate
  long _lrsStartTime = 0;
  long _lrsStartInstrs = 0;

  // counters

  /** Number of clauses that entered the unprocessed container */
  unsigned _activationLimit;
private:
  static std::pair<CompositeISE*, CompositeISEMany> createISE(Problem& prb, const Options& opt, Ordering& ordering,
     bool alascaTakesOver);

  // a "soft" time limit in deciseconds, checked manually: 0 is no limit
  unsigned _softTimeLimit = 0;
};


};

#endif /*__SaturationAlgorithm__*/

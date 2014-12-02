/**
 * @file SaturationAlgorithm.hpp
 * Defines class SaturationAlgorithm
 *
 */

#ifndef __SaturationAlgorithm__
#define __SaturationAlgorithm__

#include "SaturationAlgorithm.hpp"

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/Event.hpp"
#include "Lib/List.hpp"
#include "Lib/ScopedPtr.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/MainLoop.hpp"
#include "Kernel/RCClauseStack.hpp"
#include "Kernel/ConcurrentMainLoop.hpp"
#include "Kernel/MainLoopScheduler.hpp"
#include "Kernel/Problem.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Inferences/BackwardDemodulation.hpp"
#include "Inferences/BackwardSubsumptionResolution.hpp"
#include "Inferences/BinaryResolution.hpp"
#include "Inferences/CTFwSubsAndRes.hpp"
#include "Inferences/EqualityFactoring.hpp"
#include "Inferences/EqualityResolution.hpp"
#include "Inferences/ExtensionalityResolution.hpp"
#include "Inferences/Factoring.hpp"
#include "Inferences/ForwardDemodulation.hpp"
#include "Inferences/ForwardLiteralRewriting.hpp"
//#include "Inferences/ForwardSubsumptionAndResolution.hpp"
#include "Inferences/GlobalSubsumption.hpp"
#include "Inferences/HyperSuperposition.hpp"
//#include "Inferences/RefutationSeekerFSE.hpp"
//#include "Inferences/SLQueryForwardSubsumption.hpp"
#include "Inferences/SLQueryBackwardSubsumption.hpp"
#include "Inferences/Superposition.hpp"
#include "Inferences/URResolution.hpp"

#include "Indexing/IndexManager.hpp"

#include "Inferences/InferenceEngine.hpp"

#include "Saturation/ExtensionalityClauseContainer.hpp"
#include "Saturation/Limits.hpp"
//#include "ConsequenceFinder.hpp"
#include "Saturation/SSplitter.hpp"
//#include "SymElOutput.hpp"
//#include "AWPassiveClauseContainer.hpp"
//#include "Saturation/Discount.hpp"
//#include "Saturation/LRS.hpp"
//#include "Saturation/Otter.hpp"

#include "Shell/AnswerExtractor.hpp"

#if VDEBUG
#include<iostream>
#endif

namespace Saturation
{

//using namespace Lib;
//using namespace Kernel;
//using namespace Indexing;
//using namespace Inferences;

using Indexing::IndexManager;

using Inferences::CompositeGIE;

using Kernel::ConcurrentMainLoop;
using Kernel::MainLoop;
using Kernel::Problem;

using Shell::Options;

class SaturationAlgorithm : public MainLoop, public ConcurrentMainLoop
{
public:
  CLASS_NAME(SaturationAlgorithm);
  USE_ALLOCATOR(SaturationAlgorithm);

  static SaturationAlgorithm* createFromOptions(Problem& prb, const Options& opt, IndexManager* indexMgr=0);

  static SaturationAlgorithm* create(Problem& prb, const Options& opt);
  /*{
	  switch(opt.saturationAlgorithm()) {
	    case Shell::Options::DISCOUNT:
	      return new Discount(prb, opt);
	    case Shell::Options::LRS:
	      return new LRS(prb, opt);
	    case Shell::Options::OTTER:
	      return new Otter(prb, opt);
	    default:
	      NOT_IMPLEMENTED;
	    }
  }*/

  inline void setIndexManager(IndexManager* mgr){
	  _imgr = mgr;
  }

  inline void initIndexManager(){
	  setIndexManager(&SaturationAlgorithmContext::indexManager());
  }

  inline void initGeneratingInferenceEngine(Problem& prb, const Options& opt){
	  // create generating inference engine
	   CompositeGIE* gie=new CompositeGIE();
	   if (prb.hasEquality()) {
	     gie->addFront(new EqualityFactoring());
	     gie->addFront(new EqualityResolution());
	     gie->addFront(new Superposition());
	   }
	   gie->addFront(new Factoring());
	   if (opt.binaryResolution()) {
	     gie->addFront(new BinaryResolution());
	   }
	   if (opt.unitResultingResolution() != Options::URR_OFF) {
	     gie->addFront(new URResolution());
	   }
	   if (opt.extensionalityResolution() != Options::ER_OFF) {
	     gie->addFront(new ExtensionalityResolution());
	   }

	   setGeneratingInferenceEngine(gie);
  }

  inline void initImmediateSimplifier(){
	  _immediateSimplifier = static_cast<SaturationAlgorithmContext*>(MainLoopContext::currentContext) -> immediateSimplifier();
  }

  void initForwardSimplificationEngine(Problem& prb, const Options& opt){
	  // create forward simplification engine
	    if (opt.hyperSuperposition()) {
	      addForwardSimplifierToFront(new HyperSuperposition());
	    }
	    if (opt.globalSubsumption()) {
	      addForwardSimplifierToFront(new GlobalSubsumption());
	    }
	    if (opt.forwardLiteralRewriting()) {
	      addForwardSimplifierToFront(new ForwardLiteralRewriting());
	    }
	    if (prb.hasEquality()) {
	      switch(opt.forwardDemodulation()) {
	      case Options::DEMODULATION_ALL:
	      case Options::DEMODULATION_PREORDERED:
	        addForwardSimplifierToFront(new ForwardDemodulation());
	        break;
	      case Options::DEMODULATION_OFF:
	        break;
	  #if VDEBUG
	      default:
	        ASSERTION_VIOLATION;
	  #endif
	      }
	    }
	    if (opt.forwardSubsumption()) {
	      if (opt.forwardSubsumptionResolution()) {
	        addForwardSimplifierToFront(new CTFwSubsAndRes(true));
	      }
	      else {
	        addForwardSimplifierToFront(new CTFwSubsAndRes(false));
	      }
	    }
	    else if (opt.forwardSubsumptionResolution()) {
	      USER_ERROR("Forward subsumption resolution requires forward subsumption to be enabled.");
	    }
  }

  void initBackwardSimplificationEngine(Problem& prb, const Options& opt){
	  // create backward simplification engine
	    if (prb.hasEquality()) {
	      switch(opt.backwardDemodulation()) {
	      case Options::DEMODULATION_ALL:
	      case Options::DEMODULATION_PREORDERED:
	        addBackwardSimplifierToFront(new BackwardDemodulation());
	        break;
	      case Options::DEMODULATION_OFF:
	        break;
	  #if VDEBUG
	      default:
	        ASSERTION_VIOLATION;
	  #endif
	      }
	    }
	    if (opt.backwardSubsumption() != Options::SUBSUMPTION_OFF) {
	      bool byUnitsOnly=opt.backwardSubsumption()==Options::SUBSUMPTION_UNIT_ONLY;
	      addBackwardSimplifierToFront(new SLQueryBackwardSubsumption(byUnitsOnly));
	    }
	    if (opt.backwardSubsumptionResolution() != Options::SUBSUMPTION_OFF) {
	      bool byUnitsOnly=(opt.backwardSubsumptionResolution()==Options::SUBSUMPTION_UNIT_ONLY);
	      addBackwardSimplifierToFront(new BackwardSubsumptionResolution(byUnitsOnly));
	    }
  }

  inline void initSplitter(const Options& opt){
	  if(opt.splitting()){
	      _splitter = new SSplitter();
	  }
  }

  inline void initQuestionAnswering(const Options& opt){
	  if (opt.questionAnswering()==Options::QA_ANSWER_LITERAL) {
	     _answerLiteralManager = Shell::AnswerLiteralManager::getInstance();
	  }
  }

  void initFromOptions(Problem& prb, const Options& opt){
	   initIndexManager();
	   initGeneratingInferenceEngine(prb,opt);
	   initImmediateSimplifier();

	   initForwardSimplificationEngine(prb,opt);
	   initBackwardSimplificationEngine(prb,opt);

	   initSplitter(opt);
	   initQuestionAnswering(opt);
  }

  SaturationAlgorithm(Problem& prb, const Options& opt);
  virtual ~SaturationAlgorithm();


  //the following two functions allow to run the saturation algorithm step by step.
  void initAlgorithmRun();
  void doOneAlgorithmStep();

  UnitList* collectSaturatedSet();

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
  ExtensionalityClauseContainer* getExtensionalityClauseContainer() {
    return _extensionality;
  }

  ClauseIterator activeClauses();
  ClauseIterator passiveClauses();
  std::size_t activeClauseCount();
  std::size_t passiveClauseCount();

  Limits* getLimits() { return &_limits; }
  IndexManager* getIndexManager() { return _imgr; }
  AnswerLiteralManager* getAnswerLiteralManager() { return _answerLiteralManager; }
  Ordering& getOrdering() const { return *_ordering; }
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
  static SaturationAlgorithm* tryGetInstance() {
    CALL("SaturationAlgorithm::tryGetInstance");
    if(env->isSingleStrategy()) return s_instance;
    return static_cast<SaturationAlgorithm*>(MainLoopContext::currentContext -> getMainLoop());
  }
  static void tryUpdateFinalClauseCount();

  SSplitter* splitter() const { return _splitter; }

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
  Clause* doImmediateSimplification(Clause* cl);
  MainLoopResult saturateImpl();
  Limits _limits;
  IndexManager* _imgr;

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
  PassiveClauseContainer* _passive;
  ActiveClauseContainer* _active;
  ExtensionalityClauseContainer* _extensionality;

  ScopedPtr<GeneratingInferenceEngine> _generator;
  ImmediateSimplificationEngine* _immediateSimplifier;

  typedef List<ForwardSimplificationEngine*> FwSimplList;
  FwSimplList* _fwSimplifiers;

  typedef List<BackwardSimplificationEngine*> BwSimplList;
  BwSimplList* _bwSimplifiers;

  OrderingSP _ordering;
  ScopedPtr<LiteralSelector> _selector;

  SSplitter* _splitter;

  ConsequenceFinder* _consFinder;
  SymElOutput* _symEl;
  AnswerLiteralManager* _answerLiteralManager;


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
};

}//namespace Saturation

#endif /*__SaturationAlgorithm__*/

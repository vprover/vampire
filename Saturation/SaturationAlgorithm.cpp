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
 * @file SaturationAlgorithm.cpp
 * Implementing SaturationAlgorithm class.
 */

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/DHSet.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/SharedSet.hpp"
#include "Lib/Stack.hpp"
#include "Lib/Timer.hpp"
#include "Lib/VirtualIterator.hpp"
#include "Lib/System.hpp"
#include "Lib/STL.hpp"

#include "Indexing/LiteralIndexingStructure.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/ColorHelper.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/KBO.hpp"
#include "Kernel/LiteralSelector.hpp"
#include "Kernel/MLVariant.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/SubformulaIterator.hpp"
#include "Kernel/Unit.hpp"

#include "Inferences/InterpretedEvaluation.hpp"
#include "Inferences/PolynomialEvaluation.hpp"
#include "Inferences/PushUnaryMinus.hpp"
#include "Inferences/Cancellation.hpp"
#include "Inferences/GaussianVariableElimination.hpp"
#include "Inferences/EquationalTautologyRemoval.hpp"
#include "Inferences/Condensation.hpp"
#include "Inferences/FastCondensation.hpp"
#include "Inferences/DistinctEqualitySimplifier.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Inferences/BackwardDemodulation.hpp"
#include "Inferences/BackwardSubsumptionResolution.hpp"
#include "Inferences/BackwardSubsumptionDemodulation.hpp"
#include "Inferences/BinaryResolution.hpp"
#include "Inferences/EqualityFactoring.hpp"
#include "Inferences/EqualityResolution.hpp"
#include "Inferences/ExtensionalityResolution.hpp"
#include "Inferences/FOOLParamodulation.hpp"
#include "Inferences/Factoring.hpp"
#include "Inferences/ForwardDemodulation.hpp"
#include "Inferences/ForwardLiteralRewriting.hpp"
#include "Inferences/ForwardSubsumptionAndResolution.hpp"
#include "Inferences/ForwardSubsumptionDemodulation.hpp"
#include "Inferences/GlobalSubsumption.hpp"
#include "Inferences/HyperSuperposition.hpp"
#include "Inferences/InnerRewriting.hpp"
#include "Inferences/TermAlgebraReasoning.hpp"
#include "Inferences/SLQueryBackwardSubsumption.hpp"
#include "Inferences/Superposition.hpp"

#if VHOL
#include "Inferences/ArgCong.hpp"
#include "Inferences/NegativeExt.hpp"
#include "Inferences/PrimitiveInstantiation.hpp"
#include "Inferences/Choice.hpp"
#include "Inferences/ElimLeibniz.hpp"
#include "Inferences/CNFOnTheFly.hpp"
//#include "Inferences/RenamingOnTheFly.hpp"
#include "Inferences/BoolSimp.hpp"
#include "Inferences/CasesSimp.hpp"
#include "Inferences/Cases.hpp"
#include "Inferences/ImitateProject.hpp"
#include "Inferences/BoolEqToDiseq.hpp"
#include "Inferences/Injectivity.hpp"
#include "Inferences/BetaEtaISE.hpp"
#include "Inferences/FlexFlexSimplify.hpp"
#include "Inferences/PositiveExt.hpp"
#endif

#include "Inferences/URResolution.hpp"
#include "Inferences/Instantiation.hpp"
#include "Inferences/TheoryInstAndSimp.hpp"
#include "Inferences/Induction.hpp"
#include "Inferences/ArithmeticSubtermGeneralization.hpp"
#include "Inferences/TautologyDeletionISE.hpp"


#include "Saturation/ExtensionalityClauseContainer.hpp"

#include "Shell/AnswerExtractor.hpp"
#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/UIHelper.hpp"
#include "Shell/Shuffling.hpp"

#include "Splitter.hpp"

#include "ConsequenceFinder.hpp"
#include "LabelFinder.hpp"
#include "Splitter.hpp"
#include "SymElOutput.hpp"
#include "SaturationAlgorithm.hpp"
#include "ManCSPassiveClauseContainer.hpp"
#include "AWPassiveClauseContainer.hpp"
#include "PredicateSplitPassiveClauseContainer.hpp"
#include "Discount.hpp"
#include "LRS.hpp"
#include "Otter.hpp"

#include "NeuralPassiveClauseContainer.hpp"

#include <torch/torch.h>

using namespace Lib;
using namespace Kernel;
using namespace Shell;
using namespace Saturation;

/** Print information changes in clause containers */
#define REPORT_CONTAINERS 0
/** Print information about performed forward simplifications */
#define REPORT_FW_SIMPL 0
/** Print information about performed backward simplifications */
#define REPORT_BW_SIMPL 0


SaturationAlgorithm* SaturationAlgorithm::s_instance = 0;

std::unique_ptr<PassiveClauseContainer> makeLevel0(bool isOutermost, const Options& opt, vstring name)
{
  return std::make_unique<AWPassiveClauseContainer>(isOutermost, opt, name + "AWQ");
}

std::unique_ptr<PassiveClauseContainer> makeLevel1(bool isOutermost, bool forHO, const Options& opt, vstring name)
{
  #if VHOL
  if(opt.hoFeaturesSplitQueues() && forHO){
    Lib::vvector<std::unique_ptr<PassiveClauseContainer>> queues;
    auto cutoffs = opt.hoFeaturesSplitQueueCutoffs();
    for (unsigned i = 0; i < cutoffs.size(); i++)
    {
      auto queueName = name + "HoFSQ" + Int::toString(cutoffs[i]) + ":";
      queues.push_back(makeLevel0(false, opt, queueName));
    }
    return std::make_unique<HoFeaturesMultiSplitPassiveClauseContainer>(isOutermost, opt, name + "HoFSQ", std::move(queues));
  }
  #else
  if (opt.useTheorySplitQueues())
  {
    Lib::vvector<std::unique_ptr<PassiveClauseContainer>> queues;
    auto cutoffs = opt.theorySplitQueueCutoffs();
    for (unsigned i = 0; i < cutoffs.size(); i++)
    {
      auto queueName = name + "ThSQ" + Int::toString(cutoffs[i]) + ":";
      queues.push_back(makeLevel0(false, opt, queueName));
    }
    return std::make_unique<TheoryMultiSplitPassiveClauseContainer>(isOutermost, opt, name + "ThSQ", std::move(queues));
  }
  #endif
  else
  {
    return makeLevel0(isOutermost, opt, name);
  }
}

std::unique_ptr<PassiveClauseContainer> makeLevel2(bool isOutermost, bool forHO, const Options& opt, vstring name)
{
  if (opt.useAvatarSplitQueues())
  {
    Lib::vvector<std::unique_ptr<PassiveClauseContainer>> queues;
    auto cutoffs = opt.avatarSplitQueueCutoffs();
    for (unsigned i = 0; i < cutoffs.size(); i++)
    {
      auto queueName = name + "AvSQ" + Int::toString(cutoffs[i]) + ":";
      queues.push_back(makeLevel1(false, forHO, opt, queueName));
    }
    return std::make_unique<AvatarMultiSplitPassiveClauseContainer>(isOutermost, opt, name + "AvSQ", std::move(queues));
  }
  else
  {
    return makeLevel1(isOutermost, forHO, opt, name);
  }
}

std::unique_ptr<PassiveClauseContainer> makeLevel3(bool isOutermost, bool forHO, const Options& opt, vstring name)
{
  if (opt.useSineLevelSplitQueues())
  {
    Lib::vvector<std::unique_ptr<PassiveClauseContainer>> queues;
    auto cutoffs = opt.sineLevelSplitQueueCutoffs();
    for (unsigned i = 0; i < cutoffs.size(); i++)
    {
      auto queueName = name + "SLSQ" + Int::toString(cutoffs[i]) + ":";
      queues.push_back(makeLevel2(false, forHO, opt, queueName));
    }
    return std::make_unique<SineLevelMultiSplitPassiveClauseContainer>(isOutermost, opt, name + "SLSQ", std::move(queues));
  }
  else
  {
    return makeLevel2(isOutermost, forHO, opt, name);
  }
}

std::unique_ptr<PassiveClauseContainer> makeLevel4(bool isOutermost, bool forHO, const Options& opt, vstring name)
{
  if (opt.usePositiveLiteralSplitQueues())
  {
    Lib::vvector<std::unique_ptr<PassiveClauseContainer>> queues;
    Lib::vvector<float> cutoffs = opt.positiveLiteralSplitQueueCutoffs();
    for (unsigned i = 0; i < cutoffs.size(); i++)
    {
      auto queueName = name + "PLSQ" + Int::toString(cutoffs[i]) + ":";
      queues.push_back(makeLevel3(false, forHO, opt, queueName));
    }
    return std::make_unique<PositiveLiteralMultiSplitPassiveClauseContainer>(isOutermost, opt, name + "PLSQ", std::move(queues));
  }
  else
  {
    return makeLevel3(isOutermost, forHO, opt, name);
  }
}

/**
 * Create a SaturationAlgorithm object
 *
 * The @b passiveContainer object will be used as a passive clause container, and
 * @b selector object to select literals before clauses are activated.
 */
SaturationAlgorithm::SaturationAlgorithm(Problem& prb, const Options& opt)
  : MainLoop(prb, opt),
    _clauseActivationInProgress(false),
    _fwSimplifiers(0), _simplifiers(0), _bwSimplifiers(0), _splitter(0),
    _consFinder(0), _labelFinder(0), _symEl(0), _answerLiteralManager(0),
    _instantiation(0),
    _generatedClauseCount(0),
    _activationLimit(0)
{
  CALL("SaturationAlgorithm::SaturationAlgorithm");
  ASS_EQ(s_instance, 0);  //there can be only one saturation algorithm at a time

  BYPASSING_ALLOCATOR // because of neural things (all the torch jazz)

  _activationLimit = opt.activationLimit();

  _ordering = OrderingSP(Ordering::create(prb, opt));
  if (!Ordering::trySetGlobalOrdering(_ordering)) {
    //this is not an error, it may just lead to lower performance (and most likely not significantly lower)
    cerr << "SaturationAlgorithm cannot set its ordering as global" << endl;
  }
  _selector = LiteralSelector::getSelector(*_ordering, opt, opt.selection());

  _completeOptionSettings = opt.complete(prb);

  _unprocessed = new UnprocessedClauseContainer();

  // If we talk to prb.getProperty() here below (both in the NeuralClauseEvaluationModel constructor and when accessing the Property::FeatureIterator), it's OK, but we only get the CNF perspective.

  const vstring& ncem = opt.neuralClauseEvaluationModel();
  _neuralActivityRecoring = !opt.neuralActivityRecording().empty();
  _neuralModelGuidance = opt.neuralPassiveClauseContainer();
  if (!ncem.empty()) {
    _neuralModel = new NeuralClauseEvaluationModel(ncem.c_str(),
      std::bind(&SaturationAlgorithm::makeReadyForEval, this, std::placeholders::_1),
      // opt.neuralClauseEvaluationModelTweaks(),
      opt.randomSeed(),opt.numClauseFeatures(),opt.npccTemperature());

    if (_neuralActivityRecoring) {
      _neuralModel->setRecording();
    }

    if (_neuralModelGuidance) {
      _neuralModel->setComputing();
    }

    if (_neuralActivityRecoring || _neuralModelGuidance) {
      // must be called before setStaticFeatures
      _neuralModel->setGSD(opt.neuralClauseEvaluationModelGSD());
      _neuralModel->setStaticFeatures(prb,opt);
    }

    // will also set the strategy vector here at some point in the feature
  }

  if (_neuralModelGuidance) {
    // could also be part of level0, so that neural queues can be combined with splits
    _passive = std::make_unique<NeuralPassiveClauseContainer>(true, opt, *_neuralModel);
  }
  else if (opt.useManualClauseSelection()) {
    _passive = std::make_unique<ManCSPassiveClauseContainer>(true, opt);
  }
  else
  {
#if VHOL
    bool higher_order = prb.higherOrder();
#else
    bool higher_order = false;
#endif
    _passive = makeLevel4(true, higher_order, opt, "");
  }
  _active = new ActiveClauseContainer(opt);

  _active->attach(this);
  _passive->attach(this);

  _active->addedEvent.subscribe(this, &SaturationAlgorithm::onActiveAdded);
  _active->removedEvent.subscribe(this, &SaturationAlgorithm::activeRemovedHandler);
  _passive->addedEvent.subscribe(this, &SaturationAlgorithm::onPassiveAdded);
  _passive->removedEvent.subscribe(this, &SaturationAlgorithm::passiveRemovedHandler);
  _passive->selectedEvent.subscribe(this, &SaturationAlgorithm::onPassiveSelected);
  _unprocessed->addedEvent.subscribe(this, &SaturationAlgorithm::onUnprocessedAdded);
  _unprocessed->removedEvent.subscribe(this, &SaturationAlgorithm::onUnprocessedRemoved);
  _unprocessed->selectedEvent.subscribe(this, &SaturationAlgorithm::onUnprocessedSelected);

  if (opt.extensionalityResolution() != Options::ExtensionalityResolution::OFF) {
    _extensionality = new ExtensionalityClauseContainer(opt);
    //_active->addedEvent.subscribe(_extensionality, &ExtensionalityClauseContainer::addIfExtensionality);
  } else {
    _extensionality = 0;
  }

  s_instance=this;
}

/**
 * Destroy the SaturationAlgorithm object
 */
SaturationAlgorithm::~SaturationAlgorithm()
{
  CALL("SaturationAlgorithm::~SaturationAlgorithm");
  ASS_EQ(s_instance,this);

  s_instance=0;

  if (_splitter) {
    delete _splitter;
  }
  if (_consFinder) {
    delete _consFinder;
  }
  if (_symEl) {
    delete _symEl;
  }

  _active->detach();
  _passive->detach();

  if (_generator) {
    _generator->detach();
  }
  if (_immediateSimplifier) {
    _immediateSimplifier->detach();
  }

  while (_fwSimplifiers) {
    ForwardSimplificationEngine* fse = FwSimplList::pop(_fwSimplifiers);
    fse->detach();
    delete fse;
  }
  while (_simplifiers) {
    SimplificationEngine* fse = SimplList::pop(_simplifiers);
    fse->detach();
    delete fse;
  }
  while (_bwSimplifiers) {
    BackwardSimplificationEngine* bse = BwSimplList::pop(_bwSimplifiers);
    bse->detach();
    delete bse;
  }

  delete _unprocessed;
  delete _active;
}

void SaturationAlgorithm::tryUpdateFinalClauseCount()
{
  CALL("SaturationAlgorithm::tryUpdateFinalClauseCount");

  SaturationAlgorithm* inst = tryGetInstance();
  if (!inst) {
    return;
  }
  env.statistics->finalActiveClauses = inst->_active->sizeEstimate();
  env.statistics->finalPassiveClauses = inst->_passive->sizeEstimate();
  if (inst->_extensionality != 0) {
    env.statistics->finalExtensionalityClauses = inst->_extensionality->size();
  }
}

/**
 * Return true if the run of the prover so far is complete
 */
bool SaturationAlgorithm::isComplete()
{
  return _completeOptionSettings && !env.statistics->inferencesSkippedDueToColors;
}

ClauseIterator SaturationAlgorithm::activeClauses()
{
  CALL("SaturationAlgorithm::activeClauses");

  return _active->clauses();
}

/**
 * A function that is called when a clause is added to the active clause container.
 */
void SaturationAlgorithm::onActiveAdded(Clause* c)
{
  CALL("SaturationAlgorithm::onActiveAdded");

  if (env.options->showActive()) {
    env.beginOutput();    
    env.out() << "[SA] active: " << c->toString() << std::endl;
    env.endOutput();             
  }          
}

/**
 * A function that is called when a clause is removed from the active clause container.
 */
void SaturationAlgorithm::onActiveRemoved(Clause* c)
{
  CALL("SaturationAlgorithm::onActiveRemoved");

  ASS(c->store()==Clause::ACTIVE);
  c->setStore(Clause::NONE);
  //at this point the c object may be deleted
}

void SaturationAlgorithm::onAllProcessed()
{
  CALL("SaturationAlgorithm::onAllProcessed");
  ASS(clausesFlushed());

  if (_symEl) {
    _symEl->onAllProcessed();
  }

  if (_splitter) {
    _splitter->onAllProcessed();
  }

  if (_consFinder) {
    _consFinder->onAllProcessed();
  }
}

/*
void SaturationAlgorithm::showPredecessors(Clause* c) {
  if (c->isFromPreprocessing() ||
    _predecessorsShown.find(c->number())) return;
  vector<int64_t> parents;
  if (c->isComponent()) {
    Clause* p = _splitter->getCausalParent(c);
    ASS(p); // CAREFUL: causal parent can be none; for the ccModel thingie (we will not consider that!)
    showPredecessors(p);
    parents.push_back(p->number());
  } else {
    Inference& inf = c->inference();
    auto it1 = inf.iterator();
    while (inf.hasNext(it1)) {
      Unit* p = inf.next(it1);
      showPredecessors(p->asClause());
      parents.push_back(p->number());
    }
  }
  _neuralModel->gageEnqueue(c,parents);
  ALWAYS(_predecessorsShown.insert(c->number()));
}
*/

void SaturationAlgorithm::showPredecessorsNR(Clause* cl) {
  struct Todo {
    Clause* c;
    bool starting;
  };

  Stack<Todo> todos;
  todos.push({cl,true});
  while (todos.isNonEmpty()) {
    Todo& todo = todos.top();
    Clause* c = todo.c;
    if (todo.starting) {
      if (c->isFromPreprocessing() || _predecessorsShown.find(c->number())) {
        todos.pop();
      } else {
        todo.starting = false;
        // don't touch todo anymore, after pushing!

        if (c->isComponent()) {
          Clause* p = _splitter->getCausalParent(c);
          ASS(p); // CAREFUL: causal parent can be none; for the ccModel thingie (we will not consider that!)
          todos.push({p,true});
        } else {
          Inference& inf = c->inference();
          auto it1 = inf.iterator();
          while (inf.hasNext(it1)) {
            Unit* p = inf.next(it1);
            todos.push({p->asClause(),true});
          }
        }
      }
    } else {
      vector<int64_t> parents;
      if (c->isComponent()) {
        Clause* p = _splitter->getCausalParent(c);
        parents.push_back(p->number());
      } else {
        Inference& inf = c->inference();
        auto it1 = inf.iterator();
        while (inf.hasNext(it1)) {
          Unit* p = inf.next(it1);
          parents.push_back(p->number());
        }
      }
      _neuralModel->gageEnqueue(c,parents);
      ALWAYS(_predecessorsShown.insert(c->number()));
      todos.pop();
    }
  }
}

/*
void SaturationAlgorithm::showSubterms(Term* t) {
  if (_subtermsShown.find(t->getId())) return;
  // cout << "showSubterms for " << t->getId() << " " << t->toString() << endl;
  vector<int64_t> args;
  for (unsigned n = 0; n < t->arity(); n++) {
    TermList arg = *t->nthArgument(n);
    if (arg.isTerm()) {
      showSubterms(arg.term());
      args.push_back(arg.term()->getId()+1);
    } else {
      args.push_back(0); // all variables are 0
    }
  }
  _neuralModel->gweightEnqueueTerm(
      t->getId()+1,
      funcToSymb(t->functor()),
      0.0,
      args);
  ALWAYS(_subtermsShown.insert(t->getId()));
}
*/

void SaturationAlgorithm::showSubtermsNR(Term* t) {
  struct Todo {
    Term* t;
    bool starting;
  };

  Stack<Todo> todos;
  todos.push({t,true});
  while (todos.isNonEmpty()) {
    Todo& todo = todos.top();
    Term* t = todo.t;
    if (todo.starting) {
      if (_subtermsShown.find(t->getId())) {
        todos.pop();
      } else {
        todo.starting = false;
        // don't touch todo anymore, after pushing!
        for (unsigned n = 0; n < t->arity(); n++) {
          TermList arg = *t->nthArgument(n);
          if (arg.isTerm()) {
            todos.push({arg.term(),true});
          }
        }
      }
    } else {
      vector<int64_t> args;
      for (unsigned n = 0; n < t->arity(); n++) {
        TermList arg = *t->nthArgument(n);
        if (arg.isTerm()) {
          args.push_back(arg.term()->getId()+1);
        } else {
          args.push_back(0); // all variables are 0
        }
      }
      _neuralModel->gweightEnqueueTerm(
          t->getId()+1,
          funcToSymb(t->functor()),
          0.0,
          args);
      ALWAYS(_subtermsShown.insert(t->getId()));
      todos.pop();
    }
  }
}

void SaturationAlgorithm::showClauseLiterals(Clause* c) {
  vector<int64_t> lits;
  for (unsigned i = 0; i < c->size(); i++) {
    Literal* lit = (*c)[i];
    // using negative indices for literals (otherwise might overlap with term ids!)
    int64_t litId = -1-(int64_t)lit->getId();
    lits.push_back(litId);

    if (_literalsShown.find(lit->getId())) // and having a dedicated DHSet form them
      continue;

    vector<int64_t> args;
    for (unsigned n = 0; n < lit->arity(); n++) {
      TermList arg = *lit->nthArgument(n);
      if (arg.isTerm()) {
        showSubtermsNR(arg.term());
        args.push_back(arg.term()->getId()+1);
      } else {
        args.push_back(0); // all variables are 0
      }
    }

    _neuralModel->gweightEnqueueTerm(
        litId,
        predToSymb(lit->functor()),
        lit->isPositive() ? 1.0 : -1.0,
        args);
    ALWAYS(_literalsShown.insert(lit->getId()));
  }

  _neuralModel->gweightEnqueueClause(c,lits);
}

/*
 * Returns true, if the clause was seen for the first time.
 */
bool SaturationAlgorithm::makeReadyForEval(Clause* c) {
  if (!_shown.find(c->number())) {
    if (_neuralModel->useGage()) {
      showPredecessorsNR(c);
    }
    if (_neuralModel->useGweight()) {
      showClauseLiterals(c);
    }

    ALWAYS(_shown.insert(c->number()));
    return true;
  }
  return false;
}

/**
 * A function that is called when a clause is added to the passive clause container.
 */
void SaturationAlgorithm::onPassiveAdded(Clause* c)
{
  if (env.options->showPassive()) {
    env.beginOutput();
    env.out() << "[SA] passive: " << c->toString() << std::endl;
    env.endOutput();
  }

  if (_neuralActivityRecoring) {
    _neuralModel->journal(NeuralClauseEvaluationModel::JOURNAL_ADD,c);
  }

  //when a clause is added to the passive container,
  //we know it is not redundant
  onNonRedundantClause(c);
}

/**
 * A function that is called when a clause is removed from the active clause container.
 * The function is not called when a selected clause is removed from the passive container.
 * In this case the @b onPassiveSelected method is called.
 */
void SaturationAlgorithm::onPassiveRemoved(Clause* c)
{
  CALL("SaturationAlgorithm::onPassiveRemoved");

  if (_neuralActivityRecoring) {
    _neuralModel->journal(NeuralClauseEvaluationModel::JOURNAL_REM,c);
  }

  ASS(c->store()==Clause::PASSIVE);
  c->setStore(Clause::NONE);
  //at this point the c object can be deleted
}

/**
 * A function that is called when a clause is selected and removed from the passive
 * clause container to be activated.
 *
 * The clause @b c might not necessarily get to the activation, it can still be
 * removed by some simplification rule (in case of the Discount saturation algorithm).
 */
void SaturationAlgorithm::onPassiveSelected(Clause* c)
{
  if (_neuralActivityRecoring) {
    _neuralModel->journal(NeuralClauseEvaluationModel::JOURNAL_SEL,c);
  }
}

/**
 * A function that is called when a clause is added to the unprocessed clause container.
 */
void SaturationAlgorithm::onUnprocessedAdded(Clause* c)
{
}

/**
 * A function that is called when a clause is removed from the unprocessed clause container.
 */
void SaturationAlgorithm::onUnprocessedRemoved(Clause* c)
{
  
}

void SaturationAlgorithm::onUnprocessedSelected(Clause* c)
{
  
}


/**
 * A function that is called whenever a possibly new clause appears.
 */
void SaturationAlgorithm::onNewClause(Clause* cl)
{
  CALL("SaturationAlgorithm::onNewClause");

  if (_splitter) {
    _splitter->onNewClause(cl);
  }

  if (env.options->showNew()) {
    env.beginOutput();
    env.out() << "[SA] new: " << cl->toString() << std::endl;
    env.endOutput();
  }

  if (cl->isPropositional()) {
    onNewUsefulPropositionalClause(cl);
  }

  if (_answerLiteralManager) {
    _answerLiteralManager->onNewClause(cl);
  }
}

void SaturationAlgorithm::onNewUsefulPropositionalClause(Clause* c)
{
  CALL("SaturationAlgorithm::onNewUsefulPropositionalClause");
  ASS(c->isPropositional());
  
  if (env.options->showNewPropositional()) {
    env.beginOutput();
    env.out() << "[SA] new propositional: " << c->toString() << std::endl;
    env.endOutput();
  }

  if (_consFinder) {
    _consFinder->onNewPropositionalClause(c);
  }
  if (_labelFinder){
    _labelFinder->onNewPropositionalClause(c);
  }
}

/**
 * Called when a clause successfully passes the forward simplification
 */
void SaturationAlgorithm::onClauseRetained(Clause* cl)
{
  CALL("SaturationAlgorithm::onClauseRetained");

  //cout << "[SA] retained " << cl->toString() << endl;

}

/**
 * Called whenever a clause is simplified or deleted at any point of the
 * saturation algorithm
 */
void SaturationAlgorithm::onClauseReduction(Clause* cl, Clause** replacements, unsigned numOfReplacements,
    Clause* premise, bool forward)
{
  CALL("SaturationAlgorithm::onClauseReduction/5");
  ASS(cl);

  ClauseIterator premises;
  
  if (premise) {
    premises = pvi( getSingletonIterator(premise) );
  }
  else {
    premises=ClauseIterator::getEmpty();
  }

  onClauseReduction(cl, replacements, numOfReplacements, premises, forward);
}

void SaturationAlgorithm::onClauseReduction(Clause* cl, Clause** replacements, unsigned numOfReplacements,
    ClauseIterator premises, bool forward)
{
  CALL("SaturationAlgorithm::onClauseReduction/4");
  ASS(cl);

  static ClauseStack premStack;
  premStack.reset();
  premStack.loadFromIterator(premises);

  Clause* replacement = numOfReplacements ? *replacements : 0;

  if (env.options->showReductions()) {
    env.beginOutput();
    env.out() << "[SA] " << (forward ? "forward" : "backward") << " reduce: " << cl->toString() << endl;
    for(unsigned i = 0; i < numOfReplacements; i++){
      Clause* replacement = *replacements;
      if(replacement){ env.out() << "      replaced by " << replacement->toString() << endl; }
      replacements++;
    }
    ClauseStack::Iterator pit(premStack);
    while(pit.hasNext()){
      Clause* premise = pit.next();
      if(premise){ env.out() << "     using " << premise->toString() << endl; }
    }
    env.endOutput();
  }

  if (_splitter) {
    _splitter->onClauseReduction(cl, pvi( ClauseStack::Iterator(premStack) ), replacement);
  }

  if (replacement) {
    //Where an inference has multiple conclusions, onParenthood will only be run 
    //for the final conclusion. This is unsafe when running with symbol elimination.
    //At the moment the only simplification rules that have multiple conclusions
    //are higher-order and it is assumed that we will not run higher-order along
    //with symbol elimination.
    //In the future if a first-order simplification rule is added with multiple 
    //conclusions, this code should be updated.
    onParenthood(replacement, cl);
    while (premStack.isNonEmpty()) {
      onParenthood(replacement, premStack.pop());
    }
  }
}


void SaturationAlgorithm::onNonRedundantClause(Clause* c)
{
  CALL("SaturationAlgorithm::onNonRedundantClause");

  if (_symEl) {
    _symEl->onNonRedundantClause(c);
  }
}

/**
 * Called for clauses derived in the run of the saturation algorithm
 * for each pair clause-premise
 *
 * The propositional parts of clauses may not be set properly (the
 * clauses are always valid, however), also the function is not called
 * for clause merging (when the non-propositional parts would coincide).
 */
void SaturationAlgorithm::onParenthood(Clause* cl, Clause* parent)
{
  CALL("SaturationAlgorithm::onParenthood");

  if (_symEl) {
    _symEl->onParenthood(cl, parent);
  }
}

/**
 * This function is subscribed to the remove event of the active container
 * instead of the @b onActiveRemoved function in the constructor, as the
 * @b onActiveRemoved function is virtual.
 */
void SaturationAlgorithm::activeRemovedHandler(Clause* cl)
{
  CALL("SaturationAlgorithm::activeRemovedHandler");

  onActiveRemoved(cl);
}

/**
 * This function is subscribed to the remove event of the passive container
 * instead of the @b onPassiveRemoved function in the constructor, as the
 * @b onPassiveRemoved function is virtual.
 */
void SaturationAlgorithm::passiveRemovedHandler(Clause* cl)
{
  CALL("SaturationAlgorithm::passiveRemovedHandler");

  onPassiveRemoved(cl);
}

/**
 * Return time spent by the run of the saturation algorithm
 */
int SaturationAlgorithm::elapsedTime()
{
  return env.timer->elapsedMilliseconds()-_startTime;
}

/**
 * Add input clause @b cl into the SaturationAlgorithm object
 *
 * The clause @b cl is added into the unprocessed container, unless the
 * set-of-support option is enabled and @b cl has input type equal to
 * @b Clause::AXIOM. In this case, @b cl is put into the active container.
 */
void SaturationAlgorithm::addInputClause(Clause* cl)
{
  CALL("SaturationAlgorithm::addInputClause");
  ASS_LE(toNumber(cl->inputType()),toNumber(UnitInputType::CLAIM)); // larger input types should not appear in proof search

  if (_symEl) {
    _symEl->onInputClause(cl);
  }

  bool sosForAxioms = _opt.sos() == Options::Sos::ON || _opt.sos() == Options::Sos::ALL; 
  sosForAxioms = sosForAxioms && cl->inputType()==UnitInputType::AXIOM;

  bool sosForTheory = _opt.sos() == Options::Sos::THEORY && _opt.sosTheoryLimit() == 0;

  if (_opt.sineToAge()) {
    unsigned level = cl->getSineLevel();
    // cout << "Adding " << cl->toString() << " level " << level;
    if (level == UINT_MAX) {
      level = env.maxSineLevel-1; // as the next available (unused) value
      // cout << " -> " << level;
    }
    // cout << endl;
    cl->setAge(level);
  }

  if (sosForAxioms || (cl->isPureTheoryDescendant() && sosForTheory)){
    addInputSOSClause(cl);
  } else {
    addNewClause(cl);
  }

  if(_instantiation){
    _instantiation->registerClause(cl);
  }

  env.statistics->initialClauses++;
}

/**
 * Return literal selector that is to be used for set-of-support clauses
 */
LiteralSelector& SaturationAlgorithm::getSosLiteralSelector()
{
  CALL("SaturationAlgorithm::getSosLiteralSelector");

  if (_opt.sos() == Options::Sos::ALL || _opt.sos() == Options::Sos::THEORY) {
    if (!_sosLiteralSelector) {
      _sosLiteralSelector = new TotalLiteralSelector(getOrdering(), getOptions());
    }
    return *_sosLiteralSelector;
  }
  else {
    return *_selector;
  }
}

/**
 * Add an input set-of-support clause @b cl into the active container
 */
void SaturationAlgorithm::addInputSOSClause(Clause* cl)
{
  CALL("SaturationAlgorithm::addInputSOSClause");
  ASS_EQ(toNumber(cl->inputType()),toNumber(UnitInputType::AXIOM));

  //we add an extra reference until the clause is added to some container, so that
  //it won't get deleted during some code e.g. in the onNewClause handler
  cl->incRefCnt();

  onNewClause(cl);

simpl_start:

  Clause* simplCl=_immediateSimplifier->simplify(cl);
  if (simplCl != cl) {
    if (!simplCl) {
      onClauseReduction(cl, 0, 0, 0);
      goto fin;
    }

    simplCl->incRefCnt();
    cl->decRefCnt(); //now cl is referenced from simplCl, so after removing the extra reference, it won't be destroyed

    onNewClause(simplCl);
    onClauseReduction(cl, &simplCl, 1 , 0);
    cl=simplCl;
    goto simpl_start;
  }

  if (cl->isEmpty()) {
    addNewClause(cl);
    goto fin;
  }

  ASS(!cl->numSelected());
  {
    LiteralSelector& sosSelector = getSosLiteralSelector();
    sosSelector.select(cl);
  }

  cl->setStore(Clause::ACTIVE);
  env.statistics->activeClauses++;
  _active->add(cl);

  onSOSClauseAdded(cl);

fin:
  cl->decRefCnt();
}

void SaturationAlgorithm::runGnnOnInput()
{
  CALL("SaturationAlgorithm::runGnnOnInput");
  TIME_TRACE("gnn-eval");

  Timer::updateInstructionCount();
  long long gnn_start_instrs = Timer::elapsedInstructions();

  _numTypeCons = env.signature->typeCons();
  _numPreds = env.signature->predicates();
  ASS_EQ(_numPreds,1) // only equality in HOL!
  _numFuncs = env.signature->functions();

  constexpr auto NUM_SYMBOL_FEATURES = 24;

  // these guy must survive (in memory) until the gnnPerform call
  torch::Tensor typeCon_features = torch::empty({_numTypeCons,5}, torch::kFloat32);
  torch::Tensor symbol_features = torch::empty({_numPreds+_numFuncs,NUM_SYMBOL_FEATURES}, torch::kFloat32);

  // type constructors
  {
    float* typeCon_features_ptr = typeCon_features.data_ptr<float>();

    for (unsigned t = 0; t < _numTypeCons; t++) {
      Signature::Symbol* symb = env.signature->getTypeCon(t);
      (*typeCon_features_ptr++) = env.signature->isPlainCon(t);
      (*typeCon_features_ptr++) = env.signature->isBoolCon(t);
      (*typeCon_features_ptr++) = env.signature->isArithCon(t);
      (*typeCon_features_ptr++) = env.signature->isArrowCon(t);
      (*typeCon_features_ptr++) = symb->arity();
      // OperatorType* ot = symb->typeConType();
      // cout << "typecon: " << t << " " << env.signature->isPlainCon(t) << " " << env.signature->isBoolCon(t) << " " << env.signature->isArithCon(t) << " # " << symb->name() << endl;
      // cout << "  " << ot->toString() << " ot->arity " << ot->arity() << " symb->arity " << symb->arity() << endl;
      // cout << "  env.signature->isArrowCon(t)" << env.signature->isArrowCon(t) << endl;
    }

    _neuralModel->gnnNodeKind("typecon",typeCon_features);
  }

  // sorts correspond to the perfectly shared AtomicSort in Vampire
  unsigned sortId = 0;  // zero-based, ever growing
  vector<float> sort_features;
  DHMap<TermList,unsigned> sortsAlreadyKnown; // from termId to subtermId of the first occurrence

  vector<int64_t> srt2srt_one; // sort super-term
  vector<int64_t> srt2srt_two; // sort sub-term

  vector<int64_t> srt2typecon_one; // sort to its type constructor (for proper AtomicTerms)
  vector<int64_t> srt2typecon_two; // and back

  auto add_sort = [&](auto&& self, TermList sort) -> unsigned {
    // cout << "adding sort " << sort.toString() << endl;
    unsigned *mySortId;
    if (sortsAlreadyKnown.getValuePtr(sort,mySortId)) {
      *mySortId = sortId++;
      if (sort.isVar()) {
        // cout << "  " << sort.toString() << " is new var node" << endl;

        sort_features.push_back(1.0);
        sort_features.push_back(0.0);
        sort_features.push_back(0.0);
        sort_features.push_back(0.0);
        sort_features.push_back(0.0);
        sort_features.push_back(0.0);
      } else {
        Term *t = sort.term();
        ASS(t->isSort())

        sort_features.push_back(t->numVarOccs() > 0);   // non-ground
        sort_features.push_back(t->numVarOccs() > 2);
        sort_features.push_back(t->numVarOccs() > 4);
        sort_features.push_back(t->weight() > 1);       // non-leaf
        sort_features.push_back(t->weight() > 2);
        sort_features.push_back(t->weight() > 4);

        // will have an edge to its typeCon
        srt2typecon_one.push_back(*mySortId);
        srt2typecon_two.push_back(t->functor());

        // cout << "  " << sort.toString() << " is new term node linked to typeCon " << t->functor() << endl;

        // will have edges to sort sub-terms
        for (unsigned i = 0; i < t->arity(); i++) {
          TermList arg = *t->nthArgument(i);
          auto argId = self(self,arg);

          srt2srt_one.push_back(*mySortId);
          srt2srt_two.push_back(argId);
          // cout << "  adding sort link " << *mySortId << " - " << argId << endl;
        }
      }
    }
    // cout << "  " << sort.toString() << " is " << *mySortId << endl;
    return *mySortId;
  };

  // symbols
  {
    float* symbol_features_ptr = symbol_features.data_ptr<float>();

    vector<int64_t> symb2sort_one; // the symbs
    vector<int64_t> symb2sort_two; // their resp. (result) sorts

    vector<int64_t> symb2symb_one; // the smaller in prec
    vector<int64_t> symb2symb_two; // the larger in prec

    for (unsigned p = 0; p < _numPreds; p++) {
      (*symbol_features_ptr++) = (unsigned)(p==0);   // isEquality
      (*symbol_features_ptr++) = 1; // function symbol (KBO) weight

      (*symbol_features_ptr++) = 1; // (moral) type arity (because = is ad hoc polymorphic over one type variable)
      (*symbol_features_ptr++) = 2; // (moral) term arity (because = is term-wise binary)

      // all the rest is non-0 only for funcs
      for (unsigned i = 4; i < NUM_SYMBOL_FEATURES; i++)
        (*symbol_features_ptr++) = 0;

      // this should be the sort of equality predicate (0) and Ahmed promises there will be no other pred symbol
      ASS_EQ(p,0) // no other predicates in HOL
      TermList equalitys_poly_sort = AtomicSort::arrowSort(TermList(0, false), TermList(0, false), AtomicSort::boolSort());
      unsigned mySortId = add_sort(add_sort,equalitys_poly_sort);
      // cout << "Eq poly sort was " << equalitys_poly_sort.toString() << endl;

      // cout << "symb: " << p << " 1 1 .." << " # " << env.signature->getPredicate(p)->name() << endl;
      // cout << "symb-to-sort-for-pred: " << p << " " << mySortId << endl;
      symb2sort_one.push_back(p);
      symb2sort_two.push_back(mySortId);
    }
    {
      DArray<unsigned> predicates;
      predicates.initFromIterator(getRangeIterator(0u, _numPreds), _numPreds);
      _ordering->sortArrayByPredicatePrecedence(predicates);
      unsigned jumpLen = 1;
      do {
        unsigned prev = 0; // we hardcode = as the first predicate in the precedence (despite the precedence sometimes claiming otherwise), because = has always the smallest "level" anyway
        for (unsigned idx = 0; idx < _numPreds; idx += jumpLen) {
          if (predicates[idx] != 0) {
            // cout << "symb-prec-next: " << prev << " " << predicates[idx] << endl;
            symb2symb_one.push_back(prev);
            symb2symb_two.push_back(predicates[idx]);
            prev = predicates[idx];
          }
        }
        jumpLen *= 2;
      } while (jumpLen < _numPreds);
    }

    // cout << endl;

    auto effective_term_arity = [](TermList sort) {
      unsigned res = 0;
      while (sort.isTerm() && sort.term()->isArrowSort()) {
        res += 1;
        Term* t = sort.term();
        // cout << "  " << t->toString() << endl;
        sort = *t->nthArgument(1);
      }
      return res;
    };

    for (unsigned f = 0; f < _numFuncs; f++) {
      Signature::Symbol* symb = env.signature->getFunction(f);
      OperatorType* ot = symb->fnType();
      unsigned termArity = effective_term_arity(ot->result());

      (*symbol_features_ptr++) = 0;                             // isEquality
      (*symbol_features_ptr++) = _ordering->functionSymbolWeight(f);
      (*symbol_features_ptr++) = ot->arity();
      (*symbol_features_ptr++) = termArity;

      (*symbol_features_ptr++) = symb->introduced();
      (*symbol_features_ptr++) = symb->skolem();
      (*symbol_features_ptr++) = env.signature->isFoolConstantSymbol(false,f);
      (*symbol_features_ptr++) = env.signature->isFoolConstantSymbol(true,f);

      auto db = symb->dbIndex();
      if (db.isSome()) {
        unsigned idx = db.unwrap();
        (*symbol_features_ptr++) = (idx == 0);
        (*symbol_features_ptr++) = (idx == 1);
        (*symbol_features_ptr++) = (idx == 2);
        (*symbol_features_ptr++) = (idx > 2);
      } else {
        for (unsigned idx = 0; idx < 4; idx++)
          (*symbol_features_ptr++) = 0;
      }
      (*symbol_features_ptr++) = env.signature->isAppFun(f);
      (*symbol_features_ptr++) = env.signature->isLamFun(f);
      (*symbol_features_ptr++) = env.signature->isChoiceFun(f);

      for (unsigned proxy = 0; proxy < Signature::NOT_PROXY; proxy++) {
        (*symbol_features_ptr++) = (symb->proxy() == proxy);
      }
      // taking the result is OK everywhere in HOL (except for vAPP and vLAM who use "first-order" types, i.e. not fully curried; and are weird. But then again, they have their own features here)
      unsigned mySortId = add_sort(add_sort,symb->fnType()->result());

      /*
      cout << "symb: " << funcToSymb(f) << " e0 w" << _ordering->functionSymbolWeight(f) << " a" << ot->arity() << " ta" << termArity << " # " << symb->name() << endl;
      cout << "  fnType: " << symb->fnType()->toString() << endl;
      cout << "  i" << symb->introduced() << " s" << symb->skolem() << " f" << env.signature->isFoolConstantSymbol(false,f) << " t" << env.signature->isFoolConstantSymbol(true,f) << endl;
      cout << "  d" << symb->dbIndex() << " a" << env.signature->isAppFun(f) << " l" << env.signature->isLamFun(f) << " c" << env.signature->isChoiceFun(f) << endl;
      cout << " ";
      for (unsigned proxy = 0; proxy < Signature::NOT_PROXY; proxy++) {
        cout << " " << (symb->proxy() == proxy);
      }
      cout << endl;
      cout << "symb-to-sort: " << funcToSymb(f) << " " << mySortId << " # " << symb->fnType()->result().toString() << endl;
      cout << endl;
      */

      symb2sort_one.push_back(funcToSymb(f));
      symb2sort_two.push_back(mySortId);
      // func-to-sort: funcId sortId --- this is the output sort (input sorts can be inferred from arguments' output sorts)
    }
    {
      DArray<unsigned> functions;
      functions.initFromIterator(getRangeIterator(0u, _numFuncs), _numFuncs);
      _ordering->sortArrayByFunctionPrecedence(functions);
      unsigned jumpLen = 1;
      do {
        for (unsigned idx = jumpLen; idx < _numFuncs; idx += jumpLen) {
          // cout << "symb-prec-next: " << funcToSymb(functions[idx-jumpLen]) << " " << funcToSymb(functions[idx]) << endl;
          symb2symb_one.push_back(funcToSymb(functions[idx-jumpLen]));
          symb2symb_two.push_back(funcToSymb(functions[idx]));
        }
        jumpLen *= 2;
      } while (jumpLen < _numFuncs);
    }

    _neuralModel->gnnNodeKind("symbol",symbol_features);
    _neuralModel->gnnEdgeKind("symbol","sort",symb2sort_one,symb2sort_two);
    _neuralModel->gnnEdgeKind("symbol","symbol",symb2symb_one,symb2symb_two); // for the symbol precendence
  }

  vector<int64_t> cls2trm_one; // clauses
  vector<int64_t> cls2trm_two; // literals

  vector<int64_t> trm2trm_one; // super-term
  vector<int64_t> trm2trm_two; // sub-term

  vector<int64_t> cls2var_one; // clauses
  vector<int64_t> cls2var_two; // variable

  vector<int64_t> var2srt_one; // variable
  vector<int64_t> var2srt_two; // sort

  vector<int64_t> trm2var_one; // a subterm is a
  vector<int64_t> trm2var_two; // variable

  vector<int64_t> trm2symb_one; // a (non-var) subterm
  vector<int64_t> trm2symb_two; // has a symbol

  vector<int64_t> trm2srt_one; // resolve sort of all term's type arguments (multiple outgoing arrows possible)
  vector<int64_t> trm2srt_two; // the receiving (perfectly shared) srt id

  vector<float> clause_features;
  vector<float> term_features;
  vector<float> var_features;

  ClauseIterator toAdd = _prb.clauseIterator();
  unsigned clauseId = 0;  // zero-based, ever growing
  unsigned subtermId = 0; // zero-based, ever growing
  unsigned clVarId = 0;   // zero-based, ever growing, each clause has its own variable nodes
  DHMap<unsigned,unsigned> clauseVariables; // from clause variables (as TermList::var()) to global variables of the whole CNF (non shared)
  DHMap<unsigned,unsigned> termsAlreadyKnown; // from termId to subtermId of the first occurrence

  struct TermTodo {
    Term* trm;        // the term to iterate through
    unsigned id;      // its id (for reporting edges)
    OperatorType* ot; // trm's operator type (careful, can't be used for twoVarEquality)
    bool seenFirst;   // we want to draw an edge exactly when the superterm is seen for the first time (which implies the same for the subters, but not vice versa)
    unsigned idx = 0; // index into t's own subterms, when idx >= arity, we are done with this Todo
  };

  auto term_features_for_vars_and_weight = [&term_features](Term* t) {
    term_features.push_back(t->numVarOccs() > 0);   // non-ground
    term_features.push_back(t->numVarOccs() > 2);
    term_features.push_back(t->numVarOccs() > 4);
    term_features.push_back(t->numVarOccs() > 8);
    term_features.push_back(t->weight() > 1);       // non-leaf
    term_features.push_back(t->weight() > 4);
    term_features.push_back(t->weight() > 16);
    term_features.push_back(t->weight() > 64);
  };

  std::vector<int64_t> clauseNums;
  clauseNums.reserve(UnitList::length(_prb.units()));

  Stack<TermTodo> subterms;
  while (toAdd.hasNext()) {
    Clause* cl = toAdd.next();
    clauseNums.push_back(cl->number());
    clauseVariables.reset();
    unsigned clWeight = 0;
    for (unsigned i = 0; i < cl->size(); i++) {
      Literal* lit = (*cl)[i];
      clWeight += lit->weight();

      bool seenFirst = false;
      unsigned* sharedSubtermId;
      if (termsAlreadyKnown.getValuePtr(lit->getId(),sharedSubtermId)) {
        seenFirst = true;
        *sharedSubtermId = subtermId++;

        // each literal is a trm!
        term_features.push_back((lit->isPositive()) ? 1.0 : -1.0); // only non-zero for literals and encodes polarity
        // cout << "lit: " << *sharedSubtermId << " " << ((lit->isPositive()) ? 1.0 : -1.0) << " " << 0.0 << " ... " << lit->toString() << endl;
        term_features_for_vars_and_weight(lit);

        trm2symb_one.push_back(*sharedSubtermId);
        trm2symb_two.push_back(lit->functor());
        // cout << "trm-symb: " << *sharedSubtermId << " " << lit->functor() << endl;

        ASS_EQ(lit->functor(),0) // always just equality literals
        TermList mySort = SortHelper::getEqualityArgumentSort(lit);
        unsigned mySortId = add_sort(add_sort,mySort);
        trm2srt_one.push_back(*sharedSubtermId);
        trm2srt_two.push_back(mySortId);
        // cout << "trm-sort: " << *sharedSubtermId << " " << mySortId << " # " << mySort.toString() << endl;
      }

      // we always connect clause to its literal's term node
      cls2trm_one.push_back(clauseId);
      cls2trm_two.push_back(*sharedSubtermId);
      // cout << "cls-trm: " << clauseId << " " << *sharedSubtermId << endl;

      ASS(subterms.isEmpty());
      subterms.push({lit,*sharedSubtermId,env.signature->getPredicate(lit->functor())->predType(),seenFirst});
      while (subterms.isNonEmpty()) {
        TermTodo& top = subterms.top();

        if (top.idx < top.trm->arity()) {
          // process top.idx-th subterm of top.trm (whose gnn index is top.id)

          TermList arg = *top.trm->nthArgument(top.idx);
          // cout << "subtrm: " << arg.toString() << endl;
          // the rest of term_features will follow, depending on whether arg is a proper term or a var

          if (top.idx < top.trm->numTypeArguments()) {
            if (top.seenFirst) {
              // cout << "only a type arg, seen for the first time, connect superterm to sort and goto next arg" << endl;
              unsigned mySortId = add_sort(add_sort,arg);
              trm2srt_one.push_back(top.id);
              trm2srt_two.push_back(mySortId);
              // cout << "trm-sort: " << top.id << " " << mySortId << " # " << arg.toString() << endl;
            }
            goto next_arg;
          }

          if (arg.isTerm()) {
            Term* t = arg.term();
            // cout << "considering term arg " << t->toString() << endl;

            // under perfect sharing, we might want to skip this guy, if already exposed
            bool seenFirst = false;
            unsigned* sharedSubtermId;
            if (termsAlreadyKnown.getValuePtr(t->getId(),sharedSubtermId)) {
              seenFirst = true;
              *sharedSubtermId = subtermId++;

              term_features.push_back(0.0);   // proper subterms are not literals
              term_features_for_vars_and_weight(t);

              trm2symb_one.push_back(*sharedSubtermId);
              trm2symb_two.push_back(funcToSymb(t->functor()));
              // cout << "trm-symb: " << *sharedSubtermId << " " << funcToSymb(t->functor()) << endl;
            }
            if (top.seenFirst) {
              trm2trm_one.push_back(top.id);
              trm2trm_two.push_back(*sharedSubtermId);
              // cout << "trm-trm: " << top.id << " " << *sharedSubtermId << endl;
            }
            subterms.push({t,*sharedSubtermId,env.signature->getFunction(t->functor())->fnType(),seenFirst});
            // don't touch top anymore (push could cause reallocatio)!
          } else {
            // will be only used, if we are a var
            TermList varSort = SortHelper::getArgSort(top.trm,top.idx);

            ASS(arg.isVar());
            unsigned var = arg.var();
            unsigned* normVar;
            if (clauseVariables.getValuePtr(var,normVar)) {
              *normVar = clVarId++;
              // cout << "var: " << *normVar << " " << clauseVariables.size()-1 << endl;
              var_features.push_back(0.0); // TODO: this should be an embedding lookup
              // cls-var: clauseId varId
              // cout << "cls-var: " << clauseId << " " << *normVar << endl;       // a clause knows about its variables (and numbers them internally starting from 0)
              cls2var_one.push_back(clauseId);
              cls2var_two.push_back(*normVar);

              unsigned mySortId = add_sort(add_sort,varSort);
              // cout << "var-srt: " << *normVar << " " << mySortId << " # " << varSort.toString() << endl;          // a variable knows about its sort
              var2srt_one.push_back(*normVar);
              var2srt_two.push_back(mySortId);
            }

            // cout << "trm-var: " << top.id << " " << *normVar << endl; // this subterm is a variable
            trm2var_one.push_back(top.id);
            trm2var_two.push_back(*normVar);
          }

          next_arg: top.idx++; // next time round, will look at the next argument or die
        } else {
          subterms.pop();
        }
      }
    }

    // just register the clause and connect it with its number()
    // cout << "cls: " << clauseId << " " << cl->derivedFromGoal() << " " << cl->isTheoryAxiom() << " ... " << cl->toString() << endl;
    clause_features.push_back(cl->derivedFromGoal());
    clause_features.push_back(cl->isTheoryAxiom()); // TODO: could be more specific on which theory axiom this is (when it is one) - as was done in Deepire
    clause_features.push_back(cl->size() > 1);
    clause_features.push_back(cl->size() > 2);
    clause_features.push_back(cl->size() > 4);
    clause_features.push_back(cl->size() > 8);
    clause_features.push_back(clWeight > 4);
    clause_features.push_back(clWeight > 16);
    clause_features.push_back(clWeight > 64);
    clause_features.push_back(clWeight > 256);
    clauseId++;
  }

  // also here we (paranoidly) assume that the script module might not take any ownership of these tensors ...
  auto sort_features_t = torch::tensor(sort_features,torch::TensorOptions().dtype(torch::kFloat32)).reshape({sortId,6});

  auto clause_features_t = torch::tensor(clause_features,torch::TensorOptions().dtype(torch::kFloat32)).reshape({clauseId,10});
  auto term_features_t = torch::tensor(term_features,torch::TensorOptions().dtype(torch::kFloat32)).reshape({subtermId,9});
  auto var_features_t = torch::tensor(var_features,torch::TensorOptions().dtype(torch::kFloat32)).reshape({clVarId,1});
  // ... and so want to have them in scope until the gnnPerform call

  _neuralModel->gnnNodeKind("sort",sort_features_t);
  _neuralModel->gnnEdgeKind("sort","sort",srt2srt_one,srt2srt_two);
  _neuralModel->gnnEdgeKind("sort","typecon",srt2typecon_one,srt2typecon_two);

  /*
  cout << "sort " << sort_features_t.sizes() << endl;
  cout << "sort-typecon " << srt2typecon_one.size() << endl;
  */

  _neuralModel->gnnNodeKind("clause",clause_features_t);
  _neuralModel->gnnNodeKind("term",term_features_t);
  _neuralModel->gnnNodeKind("var",var_features_t);

  /*
  cout << "clause " << clause_features_t.sizes() << endl;
  cout << "term " << term_features_t.sizes() << endl;
  cout << "var " << var_features_t.sizes() << endl;
  */

  _neuralModel->gnnEdgeKind("clause","term",cls2trm_one,cls2trm_two);
  _neuralModel->gnnEdgeKind("term","term",trm2trm_one,trm2trm_two);      // the sub-term (down) edges
  _neuralModel->gnnEdgeKind("clause","var",cls2var_one,cls2var_two);
  _neuralModel->gnnEdgeKind("var","sort",var2srt_one,var2srt_two);
  _neuralModel->gnnEdgeKind("term","var",trm2var_one,trm2var_two);       // some subterms are variables
  _neuralModel->gnnEdgeKind("term","symbol",trm2symb_one,trm2symb_two);  // and others are proper and thus have a symbol
  _neuralModel->gnnEdgeKind("term","sort",trm2srt_one,trm2srt_two);      // those proper might also have sort arguments which we resolve

  /*
  cout << "clause-term " << cls2trm_one.size() << endl;
  cout << "term-term " << trm2trm_one.size() << endl;
  cout << "clause-var " << cls2var_one.size() << endl;
  cout << "var-sort " << var2srt_one.size() << endl;
  cout << "term-var " << trm2var_one.size() << endl;
  cout << "term-symbol " << trm2symb_one.size() << endl;
  cout << "term-sort " << trm2srt_one.size() << endl;
  */

  {
    torch::NoGradGuard no_grad; // This disables gradient computation
    _neuralModel->gnnPerform(clauseNums);
  }

  Timer::updateInstructionCount();
  env.statistics->gnnEval += (Timer::elapsedInstructions()-gnn_start_instrs);
}

/**
 * Insert clauses of the problem into the SaturationAlgorithm object
 * and initialize some internal structures.
 */
void SaturationAlgorithm::init()
{
  CALL("SaturationAlgorithm::init");

  if (_neuralActivityRecoring || _neuralModelGuidance) {
    if (_neuralModel->useGage() || _neuralModel->useGweight()) {
      BYPASSING_ALLOCATOR

      runGnnOnInput();
    }
  }

  ClauseIterator toAdd;

  if (env.options->randomTraversals()) {
    TIME_TRACE(TimeTrace::SHUFFLING);

    Stack<Clause*> aux;
    aux.loadFromIterator(_prb.clauseIterator());
    Shuffling::shuffleArray(aux,aux.size());
    toAdd = pvi(ownedArrayishIterator(std::move(aux)));
  } else {
    toAdd = _prb.clauseIterator();
  }

  while (toAdd.hasNext()) {
    Clause* cl=toAdd.next();
    addInputClause(cl);
  }

  if (_splitter) {
    _splitter->init(this);
  }
  if (_consFinder) {
    _consFinder->init(this);
  }
  if (_symEl) {
    _symEl->init(this);
  }

  _startTime=env.timer->elapsedMilliseconds();
  _startInstrs=env.timer->elapsedMegaInstructions();
}

Clause* SaturationAlgorithm::doImmediateSimplification(Clause* cl0)
{
  CALL("SaturationAlgorithm::doImmediateSimplification");
  TIME_TRACE("immediate simplification");

  static bool sosTheoryLimit = _opt.sos()==Options::Sos::THEORY;
  static unsigned sosTheoryLimitAge = _opt.sosTheoryLimit();
  static ClauseStack repStack;
  repStack.reset();

  SplitSet* splitSet = 0;

  if(sosTheoryLimit && cl0->isPureTheoryDescendant() && cl0->age() > sosTheoryLimitAge){
    return 0;
  }

  Clause* cl=cl0;

  Clause* simplCl=_immediateSimplifier->simplify(cl);
  if (simplCl != cl) {
    if (simplCl) {
      addNewClause(simplCl);
    }
    onClauseReduction(cl, &simplCl, 1, 0);
    return 0;
  }

  ClauseIterator cIt=_immediateSimplifier->simplifyMany(cl);
  if(cIt.hasNext()){
    while(cIt.hasNext()){
      Clause* simpedCl = cIt.next();
      if(!splitSet){
        splitSet = simpedCl->splits();
      } else {
        ASS(splitSet->isSubsetOf(simpedCl->splits()));
        ASS(simpedCl->splits()->isSubsetOf(splitSet));
      }
      ASS(simpedCl != cl);
      repStack.push(simpedCl);
      addNewClause(simpedCl);
    }
    onClauseReduction(cl, repStack.begin(), repStack.size(), 0);
    return 0;
  }

  return cl;
}

/**
 * Add a new clause to the saturation algorithm run
 *
 * At some point of the algorithm loop the @b newClausesToUnprocessed
 * function is called and all new clauses are added to the
 * unprocessed container.
 */
void SaturationAlgorithm::addNewClause(Clause* cl)
{
  CALL("SaturationAlgorithm::addNewClause");

  if (env.options->randomTraversals()) {
    TIME_TRACE(TimeTrace::SHUFFLING);

    Shuffling::shuffle(cl);
  }

  //we increase the reference counter here so that the clause wouldn't
  //get destroyed during handling in the onNewClause handler
  //(there the control flow goes out of the SaturationAlgorithm class,
  //so we'd better not assume on what's happening out there)
  cl->incRefCnt();
  onNewClause(cl);
  _newClauses.push(cl);
  //we can decrease the counter here -- it won't get deleted because
  //the _newClauses RC stack already took over the clause
  cl->decRefCnt();
}

void SaturationAlgorithm::newClausesToUnprocessed()
{
  CALL("SaturationAlgorithm::newClausesToUnprocessed");

  if (env.options->randomTraversals()) {
    TIME_TRACE(TimeTrace::SHUFFLING);

    Shuffling::shuffleArray(_newClauses.naked().begin(),_newClauses.size());
  }

  while (_newClauses.isNonEmpty()) {
    Clause* cl=_newClauses.popWithoutDec();
    switch(cl->store())
    {
    case Clause::UNPROCESSED:
      break;
    case Clause::PASSIVE:
      onNonRedundantClause(cl);
      break;
    case Clause::NONE:
      addUnprocessedClause(cl);
      break;
    case Clause::SELECTED:
    case Clause::ACTIVE:
#if VDEBUG
      cout << "FAIL: " << cl->toString() << endl;
      //such clauses should not appear as new ones
      cout << cl->toString() << endl;
#endif
      ASSERTION_VIOLATION_REP(cl->store());
    }
    cl->decRefCnt(); //belongs to _newClauses.popWithoutDec()
  }
}

/**
 * Return true iff there are no clauses left to be processed
 *
 * More precisely, true is returned iff the unprocessed clause
 * container and the new clause stack are empty.
 */
bool SaturationAlgorithm::clausesFlushed()
{
  return _unprocessed->isEmpty() && _newClauses.isEmpty();
}


/**
 * Perform immediate simplifications and splitting on clause @b cl and add it
 * to unprocessed.
 *
 * Forward demodulation is also being performed on @b cl.
 */
void SaturationAlgorithm::addUnprocessedClause(Clause* cl)
{
  CALL("SaturationAlgorithm::addUnprocessedClause");

  _generatedClauseCount++;
  env.statistics->generatedClauses++;

  env.checkTimeSometime<64>();


  cl=doImmediateSimplification(cl);
  if (!cl) {
    return;
  }

  if (cl->isEmpty()) {
    handleEmptyClause(cl);
    return;
  }

  cl->setStore(Clause::UNPROCESSED);
  _unprocessed->add(cl);
}

/**
 * Deal with clause that has an empty non-propositional part.
 *
 * The function receives a clause @b cl that has empty non-propositional part,
 * and returns a contradiction (an empty clause with false propositional part)
 * if it can be derived from @b cl and previously derived empty clauses.
 * Otherwise it returns 0.
 */
void SaturationAlgorithm::handleEmptyClause(Clause* cl)
{
  CALL("SaturationAlgorithm::handleEmptyClause");
  ASS(cl->isEmpty());

  if (isRefutation(cl)) {
    onNonRedundantClause(cl);

    if(cl->isPureTheoryDescendant()) {
      ASSERTION_VIOLATION_REP("A pure theory descendant is empty, which means theory axioms are inconsistent");
      reportSpiderFail();
      // this is a poor way of handling this in release mode but it prevents unsound proofs
      throw MainLoop::MainLoopFinishedException(Statistics::REFUTATION_NOT_FOUND);
    }

    //TODO - warning, derivedFromInput potentially inefficient
    if(!cl->derivedFromInput()){
      ASSERTION_VIOLATION_REP("The proof does not contain any input clauses.");
      reportSpiderFail();
      // this is a poor way of handling this in release mode but it prevents unsound proofs
      throw MainLoop::MainLoopFinishedException(Statistics::REFUTATION_NOT_FOUND);
    }
    

    // Global Subsumption doesn't set the input type the way we want so we can't do this for now
    // TODO think of a better fix
    //if(cl->inputType() == UnitInputType::AXIOM){
    if(UIHelper::haveConjecture() && !cl->derivedFromGoalCheck()){
      UIHelper::setConjectureInProof(false);
    }

    throw RefutationFoundException(cl);
  }
  // as Clauses no longer have prop parts the only reason for an empty 
  // clause not being a refutation is if it has splits

  if (_splitter && _splitter->handleEmptyClause(cl)) {
    return;
  }

  // splitter should only return false if splits isEmpty, which it cannot be
  ASSERTION_VIOLATION;
  // removed some code that dealt with the case where a clause is empty
  // but as a non-empty bdd prop part
}

/**
 * Forward-simplify the clause @b cl, return true iff the clause
 * should be retained
 *
 * If a weight-limit is imposed on clauses, it is being checked
 * by this function as well.
 */
bool SaturationAlgorithm::forwardSimplify(Clause* cl)
{
  CALL("SaturationAlgorithm::forwardSimplify");
  TIME_TRACE("forward simplification");

  if (!_passive->fulfilsAgeLimit(cl) && !_passive->fulfilsWeightLimit(cl)) {
    RSTAT_CTR_INC("clauses discarded by weight limit in forward simplification");
    env.statistics->discardedNonRedundantClauses++;
    return false;
  }

  FwSimplList::Iterator fsit(_fwSimplifiers);

  while (fsit.hasNext()) {
    ForwardSimplificationEngine* fse=fsit.next();

    {
      Clause* replacement = 0;
      ClauseIterator premises = ClauseIterator::getEmpty();

      if (fse->perform(cl,replacement,premises)) {
        if (replacement) {
          addNewClause(replacement);
        }
        onClauseReduction(cl, &replacement, 1, premises);

        return false;
      }
    }
  }

  static ClauseStack repStack;

  repStack.reset();
  SimplList::Iterator sit(_simplifiers);

  while (sit.hasNext()) {
    SimplificationEngine* se=sit.next();

    {
      ClauseIterator results = se->perform(cl);
 
      if (results.hasNext()) {
        while(results.hasNext()){
          Clause* simpedCl = results.next();
          ASS(simpedCl != cl);
          repStack.push(simpedCl);
          addNewClause(simpedCl);
        }
        onClauseReduction(cl, repStack.begin(), repStack.size(), 0);
        return false;
      }
    }
  }

  //TODO: hack that only clauses deleted by forward simplification can be destroyed (other destruction needs debugging)
  cl->incRefCnt();

  if ( _splitter && !_opt.splitAtActivation() ) {
    if (_splitter->doSplitting(cl)) {
      return false;
    }
  }

  return true;
}

/**
 * The the backward simplification with the clause @b cl.
 */
void SaturationAlgorithm::backwardSimplify(Clause* cl)
{
  CALL("SaturationAlgorithm::backwardSimplify");
  TIME_TRACE("backward simplification");


  BwSimplList::Iterator bsit(_bwSimplifiers);
  while (bsit.hasNext()) {
    BackwardSimplificationEngine* bse=bsit.next();

    BwSimplificationRecordIterator simplifications;
    bse->perform(cl,simplifications);
    while (simplifications.hasNext()) {
      BwSimplificationRecord srec=simplifications.next();
      Clause* redundant=srec.toRemove;
      ASS_NEQ(redundant, cl);

      Clause* replacement=srec.replacement;

      if (replacement) {
	addNewClause(replacement);
      }
      onClauseReduction(redundant, &replacement, 1, cl, false);

      //we must remove the redundant clause before adding its replacement,
      //as otherwise the redundant one might demodulate the replacement into
      //a tautology

      redundant->incRefCnt(); //we don't want the clause deleted before we record the simplification

      removeActiveOrPassiveClause(redundant);

      redundant->decRefCnt();
    }
  }
}

/**
 * Remove either passive or active (or reactivated, which is both)
 * clause @b cl
 *
 * In case the removal is requested during clause activation, when some indexes
 * might be traversed (and so cannot be modified), the clause deletion is postponed
 * until the clause activation is over. This is done by pushing the clause on the
 * @b _postponedClauseRemovals stack, which is then checked at the end of the
 * @b activate function.
 */
void SaturationAlgorithm::removeActiveOrPassiveClause(Clause* cl)
{
  CALL("SaturationAlgorithm::removeActiveOrPassiveClause");

  if (_clauseActivationInProgress) {
    //we cannot remove clause now, as there indexes might be traversed now,
    //and so we cannot modify them
    _postponedClauseRemovals.push(cl);
    return;
  }

  switch(cl->store()) {
  case Clause::PASSIVE:
  {
    TIME_TRACE(TimeTrace::PASSIVE_CONTAINER_MAINTENANCE);
    _passive->remove(cl);
    break;
  }
  case Clause::ACTIVE:
    _active->remove(cl);
    break;
  default:
    ASS_REP2(false, cl->store(), *cl);
  }
  //at this point the cl object can be already deleted
}

/**
 * Add clause @b c to the passive container
 */
void SaturationAlgorithm::addToPassive(Clause* cl)
{
  CALL("SaturationAlgorithm::addToPassive");
  ASS_EQ(cl->store(), Clause::UNPROCESSED);

  cl->setStore(Clause::PASSIVE);
  env.statistics->passiveClauses++;

  if (_neuralActivityRecoring && !_neuralModelGuidance) {
    // doing this specifically, for the "IMITATION" pathway
    makeReadyForEval(cl);

    static Stack<Clause*> singleton;
    singleton.push(cl);
    _neuralModel->evalClauses(singleton,/* justRecord = */ true);
    singleton.reset();
  }

  {
    TIME_TRACE(TimeTrace::PASSIVE_CONTAINER_MAINTENANCE);
    _passive->add(cl);
  }
}

void SaturationAlgorithm::removeSelected(Clause* cl)
{
  ASS_EQ(cl->store(), Clause::SELECTED);
  beforeSelectedRemoved(cl);
  cl->setStore(Clause::NONE);
}

/**
 * Activate clause @b cl
 *
 * This means putting the clause into the active container, and
 * performing generating inferences with it (in this order, so that
 * inferences such as self-superposition can happen).
 *
 * During clause activation the @b _clauseActivationInProgress value
 * is set to @b true, and clause removals by the @b removeBackwardSimplifiedClause
 * function are postponed. During the clause activation, generalisation
 * indexes should not be modified.
 */
void SaturationAlgorithm::activate(Clause* cl)
{
  CALL("SaturationAlgorithm::activate");
      TIME_TRACE("activation")

  {
  TIME_TRACE("redundancy check")
  if (_consFinder && _consFinder->isRedundant(cl)) {
    return removeSelected(cl);
  }
  }

  {
  TIME_TRACE("splitting")
  if (_splitter && _opt.splitAtActivation()) {
    if (_splitter->doSplitting(cl)) {
      return removeSelected(cl);
    }
  }
  }

  _clauseActivationInProgress=true;

  if (!cl->numSelected()) {
    TIME_TRACE("clause selection")
    TIME_TRACE("literal selection");

    if (env.options->randomTraversals()) {
      TIME_TRACE(TimeTrace::SHUFFLING);

      Shuffling::shuffle(cl);
    }

    _selector->select(cl);
  }

  ASS_EQ(cl->store(), Clause::SELECTED);
  cl->setStore(Clause::ACTIVE);
  env.statistics->activeClauses++;
  _active->add(cl);
    
  auto generated = TIME_TRACE_EXPR(TimeTrace::CLAUSE_GENERATION, _generator->generateSimplify(cl));
  auto toAdd = timeTraceIter(TimeTrace::CLAUSE_GENERATION, generated.clauses);

  while (toAdd.hasNext()) {
    Clause* genCl=toAdd.next();
    addNewClause(genCl);

    Inference::Iterator iit=genCl->inference().iterator();
    while (genCl->inference().hasNext(iit)) {
      Unit* premUnit=genCl->inference().next(iit);
      // Now we can get generated clauses having parents that are not clauses
      // Indeed, from induction we can have generated clauses whose parents do
      // not include the activated clause
      if(premUnit->isClause()){
        Clause* premCl=static_cast<Clause*>(premUnit);
        onParenthood(genCl, premCl);
      }
    }
  }

  _clauseActivationInProgress=false;

  //now we remove clauses that could not be removed during the clause activation process
  if (env.options->randomTraversals()) {
    TIME_TRACE(TimeTrace::SHUFFLING);

    Shuffling::shuffleArray(_postponedClauseRemovals.begin(),_postponedClauseRemovals.size());
  }
  while (_postponedClauseRemovals.isNonEmpty()) {
    Clause* cl=_postponedClauseRemovals.pop();
    if (cl->store() != Clause::ACTIVE && cl->store() != Clause::PASSIVE) {
      continue;
    }
    TIME_TRACE("clause removal")
    removeActiveOrPassiveClause(cl);
  }

  if (generated.premiseRedundant) {
    _active->remove(cl);
  }

  return;
}

/**
 * Perform the loop that puts clauses from the unprocessed to the passive container.
 */
void SaturationAlgorithm::doUnprocessedLoop()
{
  CALL("SaturationAlgorithm::doUnprocessedLoop");

  do {
    newClausesToUnprocessed();
    // yes, but don't try LRS with neural guidance anyway!
    if (_neuralModelGuidance && (_passive->ageLimited() || _passive->weightLimited())) {
      // so that we can start kicking out the really bad clauses already in forwardSimplify's exceedsAllLimits
      _neuralModel->bulkEval(*_unprocessed);
    }

    while (! _unprocessed->isEmpty()) {
      Clause* c = _unprocessed->pop();
      ASS(!isRefutation(c));

      if (forwardSimplify(c)) {
        onClauseRetained(c);
        addToPassive(c);
        ASS_EQ(c->store(), Clause::PASSIVE);
      }
      else {
        ASS_EQ(c->store(), Clause::UNPROCESSED);
        c->setStore(Clause::NONE);
      }

      newClausesToUnprocessed();

      if (env.timeLimitReached()) {
        throw TimeLimitExceededException();
      }
    }

    ASS(clausesFlushed());
    onAllProcessed(); // in particular, Splitter has now recomputed model which may have triggered deletions and additions
  } while (!clausesFlushed());
}

/**
 * Return true if clause can be passed to activation
 *
 * If false is returned, disposing of the clause is responsibility of
 * this function.
 */
bool SaturationAlgorithm::handleClauseBeforeActivation(Clause* c)
{
  return true;
}

/**
 * This function should be called if (and only if) we will use
 * the @c doOneAlgorithmStep() function to run the saturation
 * algorithm, instead of the @c MailLoop::run() function.
 */
void SaturationAlgorithm::initAlgorithmRun()
{
  CALL("SaturationAlgorithm::initAlgorithmRun");

  init();
}


UnitList* SaturationAlgorithm::collectSaturatedSet()
{
  CALL("SaturationAlgorithm::collectSaturatedSet");

  UnitList* res = 0;
  ClauseIterator it = _active->clauses();
  while (it.hasNext()) {
    Clause* cl = it.next();
    cl->incRefCnt();
    UnitList::push(cl, res);    
  }
  return res;
}

/**
 *
 * This function may throw RefutationFoundException and TimeLimitExceededException.
 */
void SaturationAlgorithm::doOneAlgorithmStep()
{
  CALL("SaturationAlgorithm::doOneAlgorithmStep");

  doUnprocessedLoop();

  if (_passive->isEmpty()) {
    MainLoopResult::TerminationReason termReason =
	isComplete() ? Statistics::SATISFIABLE : Statistics::REFUTATION_NOT_FOUND;
    MainLoopResult res(termReason);

    //if (termReason == Statistics::REFUTATION_NOT_FOUND){
    //  Shell::UIHelper::outputSaturatedSet(cout, pvi(UnitList::Iterator(collectSaturatedSet())));
    //}

    if (termReason == Statistics::SATISFIABLE && getOptions().proof() != Options::Proof::OFF) {
      res.saturatedSet = collectSaturatedSet();

      if (_splitter) {
        res.saturatedSet = _splitter->preprendCurrentlyAssumedComponentClauses(res.saturatedSet);
      }
    }
    throw MainLoopFinishedException(res);
  }

  Clause* cl = nullptr;
  {
    TIME_TRACE(TimeTrace::PASSIVE_CONTAINER_MAINTENANCE);
    cl = _passive->popSelected();
  }
  ASS_EQ(cl->store(),Clause::PASSIVE);
  cl->setStore(Clause::SELECTED);

  if (!handleClauseBeforeActivation(cl)) {
    return;
  }

  activate(cl);
}


/**
 * Perform saturation on clauses that were added through
 * @b addInputClauses function
 */
MainLoopResult SaturationAlgorithm::runImpl()
{
  CALL("SaturationAlgorithm::runImpl");

  unsigned l = 0;
  try
  {
    for (;;l++) {
      if (_activationLimit && l > _activationLimit) {
        throw ActivationLimitExceededException();
      }

      doOneAlgorithmStep();

      Timer::syncClock();
      if (env.timeLimitReached()) {
        throw TimeLimitExceededException();
      }

      env.statistics->activations = l;
    }
  } catch(const RefutationFoundException& r) {
    if (_neuralActivityRecoring) {
      Timer::setLimitEnforcement(false);
      saveNeuralActivity(r.refutation);
    }

    throw;
  } catch (const ThrowableBase&) {
    tryUpdateFinalClauseCount();
    throw;
  }
}

void SaturationAlgorithm::saveNeuralActivity(Clause* refutation)
{
  CALL("SaturationAlgorithm::saveNeuralActivity");

  DHSet<Unit*> done; // will contain the processed proof units
  refutation->minimizeAncestorsAndUpdateSelectedStats(done);

  std::vector<int64_t> proof_units;
  auto it = done.iterator();
  while (it.hasNext()) {
    proof_units.push_back(it.next()->number());
  }
  _neuralModel->setProofUnitsAndSaveRecorded(proof_units,
    env.options->neuralActivityRecording().c_str());
}

/**
 * Assign an generating inference object @b generator to be used
 *
 * This object takes ownership of the @b generator object
 * and will be responsible for its deletion.
 *
 * To use multiple generating inferences, use the @b CompositeGIE
 * object.
 */
void SaturationAlgorithm::setGeneratingInferenceEngine(SimplifyingGeneratingInference* generator)
{
  CALL("SaturationAlgorithm::setGeneratingInferenceEngine");

  ASS(!_generator);
  _generator=generator;
  _generator->attach(this);
}

/**
 * Assign an immediate simplifier object @b immediateSimplifier
 * to be used
 *
 * This object takes ownership of the @b immediateSimplifier object
 * and will be responsible for its deletion.
 *
 * For description of what an immediate simplifier is, see
 * @b ImmediateSimplificationEngine documentation.
 *
 * To use multiple immediate simplifiers, use the @b CompositeISE
 * object.
 */
void SaturationAlgorithm::setImmediateSimplificationEngine(ImmediateSimplificationEngine* immediateSimplifier)
{
  CALL("SaturationAlgorithm::setImmediateSimplificationEngine");

  ASS(!_immediateSimplifier);
  _immediateSimplifier=immediateSimplifier;
  _immediateSimplifier->attach(this);
}

/**
 * Add a forward simplifier, so that it is applied before the
 * simplifiers that were added before it. The object takes ownership
 * of the forward simplifier and will take care of destroying it.
 *
 * Forward demodulation simplifier should be added by the
 * @b setFwDemodulator function, not by this one.
 */
void SaturationAlgorithm::addForwardSimplifierToFront(ForwardSimplificationEngine* fwSimplifier)
{
  FwSimplList::push(fwSimplifier, _fwSimplifiers);
  fwSimplifier->attach(this);
}

void SaturationAlgorithm::addSimplifierToFront(SimplificationEngine* simplifier)
{
  SimplList::push(simplifier, _simplifiers);
  simplifier->attach(this);
}

/**
 * Add a backward simplifier, so that it is applied before the
 * simplifiers that were added before it. The object takes ownership
 * of the backward simplifier and will take care of destroying it.
 */
void SaturationAlgorithm::addBackwardSimplifierToFront(BackwardSimplificationEngine* bwSimplifier)
{
  BwSimplList::push(bwSimplifier, _bwSimplifiers);
  bwSimplifier->attach(this);
}

/**
 * @since 05/05/2013 Manchester, splitting changed to new values
 * @author Andrei Voronkov
 */
SaturationAlgorithm* SaturationAlgorithm::createFromOptions(Problem& prb, const Options& opt, IndexManager* indexMgr)
{
  CALL("SaturationAlgorithm::createFromOptions");

  SaturationAlgorithm* res;
  switch(opt.saturationAlgorithm()) {
  case Shell::Options::SaturationAlgorithm::DISCOUNT:
    res=new Discount(prb, opt);
    break;
  case Shell::Options::SaturationAlgorithm::LRS:
    res=new LRS(prb, opt);
    break;
  case Shell::Options::SaturationAlgorithm::OTTER:
    res=new Otter(prb, opt);
    break;
  default:
    NOT_IMPLEMENTED;
  }
  if (indexMgr) {
    res->_imgr = SmartPtr<IndexManager>(indexMgr, true);
    indexMgr->setSaturationAlgorithm(res);
  }
  else {
    res->_imgr = SmartPtr<IndexManager>(new IndexManager(res));
  }

  if(opt.splitting()){
    res->_splitter = new Splitter();
  }

  // create generating inference engine
  CompositeGIE* gie=new CompositeGIE();

  //TODO here induction is last, is that right?
  if(opt.induction()!=Options::Induction::NONE){
    gie->addFront(new Induction());
  }

  if(opt.instantiation()!=Options::Instantiation::OFF){
    res->_instantiation = new Instantiation();
    //res->_instantiation->init();
    gie->addFront(res->_instantiation);
  }

  if (prb.hasEquality() || opt.FOOLParamodulation()
#if VHOL // cases and foolParamodulation can introduce equality into a problem which has none
  ||  opt.cases()
#endif
    ) {
    gie->addFront(new EqualityFactoring());
    gie->addFront(new EqualityResolution());
#if VHOL
    if(env.options->superposition()){
#endif
      gie->addFront(new Superposition());
#if VHOL
    }
#endif
  } else if(opt.unificationWithAbstraction()!=Options::UnificationWithAbstraction::OFF){
    gie->addFront(new EqualityResolution()); 
  }

#if VHOL
  if(prb.higherOrder()){
    gie->addFront(new ArgCong());
    gie->addFront(new NegativeExt());//TODO add option
    if(!env.options->higherOrderUnifDepth() && !env.options->applicativeUnify()){
      // only add when we are not carrying out higher-order unification
      gie->addFront(new ImitateProject());
    } 
    if(env.options->positiveExtensionality()){
      gie->addFront(new PositiveExt());
    }
    if(prb.hasFOOL() && env.options->booleanEqTrick()){
      gie->addFront(new BoolEqToDiseq());
    }
    if(env.options->choiceReasoning()){
      gie->addFront(new Choice());
    }
  }

  if(opt.complexBooleanReasoning() && prb.hasBoolVar() && prb.higherOrder()){
    gie->addFront(new PrimitiveInstantiation()); //TODO only add in some cases
    gie->addFront(new ElimLeibniz());
  }

  if (opt.cases() && prb.hasFOOL()) {
    gie->addFront(new Cases());
  }

  if((prb.hasLogicalProxy() || prb.hasBoolVar() || prb.hasFOOL()) &&
      prb.higherOrder() && !prb.quantifiesOverPolymorphicVar()){ // TODO why the last condition????
    if(env.options->cnfOnTheFly() != Options::CNFOnTheFly::EAGER && 
       env.options->cnfOnTheFly() != Options::CNFOnTheFly::OFF){
      gie->addFront(new LazyClausificationGIE());
    }
  }    

  if (prb.higherOrder() && opt.injectivityReasoning()) {
    gie->addFront(new Injectivity());
  }
#endif

  gie->addFront(new Factoring());
  if (opt.binaryResolution()) {
    gie->addFront(new BinaryResolution());
  }
  if (opt.unitResultingResolution() != Options::URResolution::OFF) {
#if VHOL
    if(env.property->higherOrder()){
      // TODO Should we be outputing an error or just dying?
      if (outputAllowed()) {
        env.beginOutput();
        addCommentSignForSZS(env.out());
        env.out() << "WARNING: unit resulting resolution is not compatible with higher-order. Ignoring request." << endl;
        env.endOutput();
      }            
    } else {
#endif
      gie->addFront(new URResolution());
#if VHOL
    }
#endif  
  }
  if (opt.extensionalityResolution() != Options::ExtensionalityResolution::OFF) {
    gie->addFront(new ExtensionalityResolution());
  }
  if (opt.FOOLParamodulation()) {
#if VHOL
    if(env.property->higherOrder()){
      if (outputAllowed()) {
        env.beginOutput();
        addCommentSignForSZS(env.out());
        env.out() << "WARNING: FOOL paramodulation is not compatible with higher-order. Try using Cases or CasesSimp instead. Ignoring request." << endl;
        env.endOutput();
      } 
    } else {
#endif
      gie->addFront(new FOOLParamodulation());
#if VHOL
    }
#endif    
  }

  if(prb.hasEquality() && env.signature->hasTermAlgebras()) {
    if (opt.termAlgebraCyclicityCheck() == Options::TACyclicityCheck::RULE) {
      gie->addFront(new AcyclicityGIE());
    } else if (opt.termAlgebraCyclicityCheck() == Options::TACyclicityCheck::RULELIGHT) {
      gie->addFront(new AcyclicityGIE1());
    }
    if (opt.termAlgebraInferences()) {
      gie->addFront(new InjectivityGIE());
    }
  }

  CompositeSGI* sgi = new CompositeSGI();
  sgi->push(gie);

  auto& ordering = res->getOrdering();

  if (opt.evaluationMode() == Options::EvaluationMode::POLYNOMIAL_CAUTIOUS) {
    sgi->push(new PolynomialEvaluation(ordering));
  }

  if (env.options->cancellation() == Options::ArithmeticSimplificationMode::CAUTIOUS) {
    sgi->push(new Cancellation(ordering)); 
  }

  if (env.options->gaussianVariableElimination() == Options::ArithmeticSimplificationMode::CAUTIOUS) {
    sgi->push(new LfpRule<GaussianVariableElimination>(GaussianVariableElimination())); 
  }

  if (env.options->arithmeticSubtermGeneralizations() == Options::ArithmeticSimplificationMode::CAUTIOUS) {
    for (auto gen : allArithmeticSubtermGeneralizations())  {
      sgi->push(gen);
    }
  }


#if VZ3
  if (opt.theoryInstAndSimp() != Shell::Options::TheoryInstSimp::OFF){
    sgi->push(new TheoryInstAndSimp());
  }
#endif

  res->setGeneratingInferenceEngine(sgi);

  res->setImmediateSimplificationEngine(createISE(prb, opt, res->getOrdering()));

  //create simplification engine

#if VHOL
  if((prb.hasLogicalProxy() || prb.hasBoolVar() || prb.hasFOOL()) &&
      prb.higherOrder() && !prb.quantifiesOverPolymorphicVar()){
    if(env.options->cnfOnTheFly() != Options::CNFOnTheFly::EAGER &&
       env.options->cnfOnTheFly() != Options::CNFOnTheFly::OFF){
      res->addSimplifierToFront(new LazyClausification());
    }
  }  
#endif

  // create forward simplification engine
  if (prb.hasEquality() && opt.innerRewriting()) {
    res->addForwardSimplifierToFront(new InnerRewriting());
  }
  if (opt.hyperSuperposition()) {
#if VHOL
    if(env.property->higherOrder()){
      // TODO how to output error properly?
      // Should we be outputing an error or just dying?
      if (outputAllowed()) {
        env.beginOutput();
        addCommentSignForSZS(env.out());
         env.out() << "WARNING: hyper superposition is not compatible with higher-order. Ignoring request" << endl;
        env.endOutput();
      }      
    } else {
#endif    
      res->addForwardSimplifierToFront(new HyperSuperposition());
#if VHOL
    }
#endif    
  }
  if (opt.globalSubsumption()) {
    res->addForwardSimplifierToFront(new GlobalSubsumption(opt));
  }
  if (opt.forwardLiteralRewriting()) {
    res->addForwardSimplifierToFront(new ForwardLiteralRewriting());
  }
  if (prb.hasEquality()) {
    // NOTE:
    // fsd should be performed after forward subsumption,
    // because every successful forward subsumption will lead to a (useless) match in fsd.
    if (opt.forwardSubsumptionDemodulation()) {
#if VHOL    
      if(prb.higherOrder()){
        res->addForwardSimplifierToFront(new ForwardSubsumptionDemodulation<DemodulationSubtermIt>(false));
      } else {
#endif
        res->addForwardSimplifierToFront(new ForwardSubsumptionDemodulation<NonVariableNonTypeIterator>(false));
#if VHOL
     }
#endif    
    }
  }
  if (prb.hasEquality()) {
    switch(opt.forwardDemodulation()) {
    case Options::Demodulation::ALL:
    case Options::Demodulation::PREORDERED:
#if VHOL    
      if(prb.higherOrder()){
        res->addForwardSimplifierToFront(new ForwardDemodulation<DemodulationSubtermIt>());
      } else {
#endif
        res->addForwardSimplifierToFront(new ForwardDemodulation<NonVariableNonTypeIterator>());
#if VHOL
      }
#endif
      break;
    case Options::Demodulation::OFF:
      break;
#if VDEBUG
    default:
      ASSERTION_VIOLATION;
#endif
    }
  }
  if (opt.forwardSubsumption()) {
    //res->addForwardSimplifierToFront(new CTFwSubsAndRes(true));
    bool withResolution = opt.forwardSubsumptionResolution();
    res->addForwardSimplifierToFront(new ForwardSubsumptionAndResolution(withResolution));
  }
  else if (opt.forwardSubsumptionResolution()) {
    USER_ERROR("Forward subsumption resolution requires forward subsumption to be enabled.");
  }

  // create backward simplification engine
  if (prb.hasEquality()) {
    switch(opt.backwardDemodulation()) {
    case Options::Demodulation::ALL:
    case Options::Demodulation::PREORDERED:
#if VHOL
      if(prb.higherOrder()){
        res->addBackwardSimplifierToFront(new BackwardDemodulation<DemodulationSubtermIt>());
      } else {
#endif
        res->addBackwardSimplifierToFront(new BackwardDemodulation<NonVariableNonTypeIterator>());        
#if VHOL
      }
#endif
      break;
    case Options::Demodulation::OFF:
      break;
#if VDEBUG
    default:
      ASSERTION_VIOLATION;
#endif
    }
  }
  if (prb.hasEquality() && opt.backwardSubsumptionDemodulation()) {
#if VHOL
      if(prb.higherOrder()){
        res->addBackwardSimplifierToFront(new BackwardSubsumptionDemodulation<DemodulationSubtermIt>());
      } else {
#endif    
        res->addBackwardSimplifierToFront(new BackwardSubsumptionDemodulation<NonVariableNonTypeIterator>());
#if VHOL
      }
#endif      
  }
  if (opt.backwardSubsumption() != Options::Subsumption::OFF) {
    bool byUnitsOnly=opt.backwardSubsumption()==Options::Subsumption::UNIT_ONLY;
    res->addBackwardSimplifierToFront(new SLQueryBackwardSubsumption(byUnitsOnly));
  }
  if (opt.backwardSubsumptionResolution() != Options::Subsumption::OFF) {
    bool byUnitsOnly=opt.backwardSubsumptionResolution()==Options::Subsumption::UNIT_ONLY;
    res->addBackwardSimplifierToFront(new BackwardSubsumptionResolution(byUnitsOnly));
  }

  if (opt.mode()==Options::Mode::CONSEQUENCE_ELIMINATION) {
    res->_consFinder=new ConsequenceFinder();
  }
  if (opt.showSymbolElimination()) {
    res->_symEl=new SymElOutput();
  }
  if (opt.questionAnswering()==Options::QuestionAnsweringMode::ANSWER_LITERAL) {
    res->_answerLiteralManager = AnswerLiteralManager::getInstance();
  }
  return res;
} // SaturationAlgorithm::createFromOptions


/**
 * Create local clause simplifier for problem @c prb according to options @c opt
 */
ImmediateSimplificationEngine* SaturationAlgorithm::createISE(Problem& prb, const Options& opt, Ordering& ordering)
{
  CALL("MainLoop::createImmediateSE");

  CompositeISE* res=new CompositeISE();

  if(prb.hasEquality() && opt.equationalTautologyRemoval()) {
    res->addFront(new EquationalTautologyRemoval());
  }

  switch(opt.condensation()) {
  case Options::Condensation::ON:
    res->addFront(new Condensation());
    break;
  case Options::Condensation::FAST:
    res->addFront(new FastCondensation());
    break;
  case Options::Condensation::OFF:
    break;
  }

#if VHOL
  if(prb.higherOrder() && env.options->choiceReasoning()){
    res->addFront(new ChoiceDefinitionISE());
  }

  if((prb.hasLogicalProxy() || prb.hasBoolVar() || prb.hasFOOL()) &&
      prb.higherOrder() && !env.options->addProxyAxioms()){

    if(env.options->cnfOnTheFly() == Options::CNFOnTheFly::EAGER){
      res->addFrontMany(new EagerClausificationISE());
    }
    if(env.options->iffXorRewriter()){
      res->addFront(new IFFXORRewriterISE());
    }
    res->addFront(new BoolSimp());
  }

  if (prb.hasFOOL() && opt.casesSimp() && !opt.cases()) {
    res->addFrontMany(new CasesSimp());
  }

  if(prb.higherOrder() && env.options->newTautologyDel()){
    res->addFront(new TautologyDeletionISE2());
  }  

  if(prb.higherOrder()){
    res->addFront(new BetaEtaSimplify());
    res->addFront(new FlexFlexSimplify());
  }
#endif

  // Only add if there are distinct groups 
  if(prb.hasEquality() && env.signature->hasDistinctGroups()) {
    res->addFront(new DistinctEqualitySimplifier());
  }
  if(prb.hasEquality() && env.signature->hasTermAlgebras()) {
    if (opt.termAlgebraInferences()) {
      res->addFront(new DistinctnessISE());
      res->addFront(new InjectivityISE());
      res->addFront(new NegativeInjectivityISE());
    }
  }
  if(prb.hasInterpretedOperations() || prb.hasNumerals()) {
    if (env.options->arithmeticSubtermGeneralizations() == Options::ArithmeticSimplificationMode::FORCE) {
      for (auto gen : allArithmeticSubtermGeneralizations())  {
        res->addFront(&gen->asISE());
      }
    }

    if (env.options->gaussianVariableElimination() == Options::ArithmeticSimplificationMode::FORCE) {
      res->addFront(&(new GaussianVariableElimination())->asISE()); 
    }

    if (env.options->cancellation() == Options::ArithmeticSimplificationMode::FORCE) {
      res->addFront(&(new Cancellation(ordering))->asISE()); 
    }

    switch (env.options->evaluationMode()) {
      case Options::EvaluationMode::SIMPLE: 
        res->addFront(new InterpretedEvaluation(env.options->inequalityNormalization(), ordering));
        break;
      case Options::EvaluationMode::POLYNOMIAL_FORCE:
        res->addFront(&(new PolynomialEvaluation(ordering))->asISE());
        break;
      case Options::EvaluationMode::POLYNOMIAL_CAUTIOUS:
        break;
    }

    if (env.options->pushUnaryMinus()) {
      res->addFront(new PushUnaryMinus()); 
    }

  }
  if(prb.hasEquality()) {
    res->addFront(new TrivialInequalitiesRemovalISE());
  }
  res->addFront(new TautologyDeletionISE());
  res->addFront(new DuplicateLiteralRemovalISE());

  return res;
}


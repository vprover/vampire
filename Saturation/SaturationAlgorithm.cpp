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

#define USING_LIBTORCH // see Lib/Output.hpp

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/DHSet.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/SharedSet.hpp"
#include "Lib/Stack.hpp"
#include "Lib/Timer.hpp"
#include "Lib/VirtualIterator.hpp"
#include "Lib/System.hpp"

#include "Indexing/LiteralIndexingStructure.hpp"

#include "Kernel/Clause.hpp"
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
#include "Inferences/BackwardSubsumptionAndResolution.hpp"
#include "Inferences/BackwardSubsumptionDemodulation.hpp"
#include "Inferences/BinaryResolution.hpp"
#include "Inferences/CodeTreeForwardSubsumptionAndResolution.hpp"
#include "Inferences/EqualityFactoring.hpp"
#include "Inferences/EqualityResolution.hpp"
#include "Inferences/BoolEqToDiseq.hpp"
#include "Inferences/ExtensionalityResolution.hpp"
#include "Inferences/FOOLParamodulation.hpp"
#include "Inferences/Injectivity.hpp"
#include "Inferences/Factoring.hpp"
#include "Inferences/FunctionDefinitionRewriting.hpp"
#include "Inferences/ForwardDemodulation.hpp"
#include "Inferences/ForwardLiteralRewriting.hpp"
#include "Inferences/ForwardSubsumptionAndResolution.hpp"
#include "Inferences/InvalidAnswerLiteralRemovals.hpp"
#include "Inferences/ForwardSubsumptionDemodulation.hpp"
#include "Inferences/GlobalSubsumption.hpp"
#include "Inferences/InnerRewriting.hpp"
#include "Inferences/TermAlgebraReasoning.hpp"
#include "Inferences/Superposition.hpp"
#include "Inferences/ArgCong.hpp"
#include "Inferences/NegativeExt.hpp"
#include "Inferences/Narrow.hpp"
#include "Inferences/PrimitiveInstantiation.hpp"
#include "Inferences/Choice.hpp"
#include "Inferences/ElimLeibniz.hpp"
#include "Inferences/SubVarSup.hpp"
#include "Inferences/CNFOnTheFly.hpp"
#include "Inferences/URResolution.hpp"
#include "Inferences/Instantiation.hpp"
#include "Inferences/TheoryInstAndSimp.hpp"
#include "Inferences/Induction.hpp"
#include "Inferences/ArithmeticSubtermGeneralization.hpp"
#include "Inferences/TautologyDeletionISE.hpp"
#include "Inferences/CombinatorDemodISE.hpp"
#include "Inferences/CombinatorNormalisationISE.hpp"
#include "Inferences/BoolSimp.hpp"
#include "Inferences/CasesSimp.hpp"
#include "Inferences/Cases.hpp"
#include "Inferences/DefinitionIntroduction.hpp"

#include "Saturation/ExtensionalityClauseContainer.hpp"

#include "Shell/AnswerLiteralManager.hpp"
#include "Shell/ConditionalRedundancyHandler.hpp"
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
#include "AWPassiveClauseContainers.hpp"
#include "PredicateSplitPassiveClauseContainers.hpp"
#include "Discount.hpp"
#include "LRS.hpp"
#include "Otter.hpp"

#include "NeuralPassiveClauseContainers.hpp"

#include <iomanip>

using namespace std;
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

std::unique_ptr<PassiveClauseContainer> makeLevel0(bool isOutermost, const Options& opt, std::string name)
{
  if (opt.weightRatio() == 0) {
    ASS_G(opt.ageRatio(),0);
    return std::make_unique<AgeBasedPassiveClauseContainer>(isOutermost, opt, name + "AgeQ");
  } else if (opt.ageRatio() == 0) {
    return std::make_unique<WeightBasedPassiveClauseContainer>(isOutermost, opt, name + "WeightQ");
  }
  return std::make_unique<AWPassiveClauseContainer>(isOutermost, opt, name + "AWQ");
}

std::unique_ptr<PassiveClauseContainer> makeLevel1(bool isOutermost, const Options& opt, std::string name)
{
  if (opt.useTheorySplitQueues()) {
    std::vector<std::unique_ptr<PassiveClauseContainer>> queues;
    auto cutoffs = opt.theorySplitQueueCutoffs();
    for (unsigned i = 0; i < cutoffs.size(); i++) {
      auto queueName = name + "ThSQ" + Int::toString(cutoffs[i]) + ":";
      queues.push_back(makeLevel0(false, opt, queueName));
    }
    return std::make_unique<TheoryMultiSplitPassiveClauseContainer>(isOutermost, opt, name + "ThSQ", std::move(queues));
  }
  else {
    return makeLevel0(isOutermost, opt, name);
  }
}

std::unique_ptr<PassiveClauseContainer> makeLevel2(bool isOutermost, const Options& opt, std::string name)
{
  if (opt.useAvatarSplitQueues()) {
    std::vector<std::unique_ptr<PassiveClauseContainer>> queues;
    auto cutoffs = opt.avatarSplitQueueCutoffs();
    for (unsigned i = 0; i < cutoffs.size(); i++) {
      auto queueName = name + "AvSQ" + Int::toString(cutoffs[i]) + ":";
      queues.push_back(makeLevel1(false, opt, queueName));
    }
    return std::make_unique<AvatarMultiSplitPassiveClauseContainer>(isOutermost, opt, name + "AvSQ", std::move(queues));
  }
  else {
    return makeLevel1(isOutermost, opt, name);
  }
}

std::unique_ptr<PassiveClauseContainer> makeLevel3(bool isOutermost, const Options& opt, std::string name)
{
  if (opt.useSineLevelSplitQueues()) {
    std::vector<std::unique_ptr<PassiveClauseContainer>> queues;
    auto cutoffs = opt.sineLevelSplitQueueCutoffs();
    for (unsigned i = 0; i < cutoffs.size(); i++) {
      auto queueName = name + "SLSQ" + Int::toString(cutoffs[i]) + ":";
      queues.push_back(makeLevel2(false, opt, queueName));
    }
    return std::make_unique<SineLevelMultiSplitPassiveClauseContainer>(isOutermost, opt, name + "SLSQ", std::move(queues));
  }
  else {
    return makeLevel2(isOutermost, opt, name);
  }
}

std::unique_ptr<PassiveClauseContainer> makeLevel4(bool isOutermost, const Options& opt, std::string name)
{
  if (opt.usePositiveLiteralSplitQueues()) {
    std::vector<std::unique_ptr<PassiveClauseContainer>> queues;
    std::vector<float> cutoffs = opt.positiveLiteralSplitQueueCutoffs();
    for (unsigned i = 0; i < cutoffs.size(); i++) {
      auto queueName = name + "PLSQ" + Int::toString(cutoffs[i]) + ":";
      queues.push_back(makeLevel3(false, opt, queueName));
    }
    return std::make_unique<PositiveLiteralMultiSplitPassiveClauseContainer>(isOutermost, opt, name + "PLSQ", std::move(queues));
  }
  else {
    return makeLevel3(isOutermost, opt, name);
  }
}

std::unique_ptr<PassiveClauseContainer> makeLevel5(bool isOutermost, const Options& opt, std::string name, NeuralClauseEvaluationModel* neuralModel)
{
  if (opt.useNeuralEvalSplitQueues()) {
    std::vector<std::unique_ptr<PassiveClauseContainer>> queues;
    std::vector<float> cutoffs = opt.neuralEvalSplitQueueCutoffs();
    for (unsigned i = 0; i < cutoffs.size(); i++) {
      auto queueName = name + "NLSQ" + Int::toString(cutoffs[i]) + ":";
      queues.push_back(makeLevel4(false, opt, queueName));
    }
    return std::make_unique<NeuralEvalSplitPassiveClauseContainer>(isOutermost, opt, name + "NLSQ", std::move(queues), *neuralModel);
  }
  else {
    return makeLevel4(isOutermost, opt, name);
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
    _instantiation(0), _fnDefHandler(prb.getFunctionDefinitionHandler()),
    _generatedClauseCount(0),
    _activationLimit(0)
{
  ASS_EQ(s_instance, 0);  //there can be only one saturation algorithm at a time

  _activationLimit = opt.activationLimit();

  _ordering = OrderingSP(Ordering::create(prb, opt));
  if (!Ordering::trySetGlobalOrdering(_ordering)) {
    // this is not an error, it may just lead to lower performance (and most likely not significantly lower)
    cerr << "SaturationAlgorithm cannot set its ordering as global" << endl;
  }
  _selector = LiteralSelector::getSelector(*_ordering, opt, opt.selection());

  _completeOptionSettings = opt.complete(prb);

  _unprocessed = new UnprocessedClauseContainer();

  // If we talk to prb.getProperty() here below (both in the NeuralClauseEvaluationModel constructor and when accessing the Property::FeatureIterator), it's OK, but we only get the CNF perspective.

  const std::string& ncem = opt.neuralClauseEvaluationModel();
  _neuralActivityRecoring = !opt.neuralActivityRecording().empty();
  _neuralModelGuidance = opt.neuralPassiveClauseContainer();
  if (!ncem.empty()) {
    _neuralModel = new NeuralClauseEvaluationModel(ncem,
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
  else {
    _passive = makeLevel5(true, opt, "", _neuralModel.ptr());
  }
  _active = new ActiveClauseContainer();

  _active->attach(this);
  _passive->attach(this);

  _active->addedEvent.subscribe(this, &SaturationAlgorithm::onActiveAdded);
  _active->removedEvent.subscribe(this, &SaturationAlgorithm::activeRemovedHandler);
  _passive->addedEvent.subscribe(this, &SaturationAlgorithm::onPassiveAdded);
  _passive->removedEvent.subscribe(this, &SaturationAlgorithm::passiveRemovedHandler);
  _passive->selectedEvent.subscribe(this, &SaturationAlgorithm::onPassiveSelected);

  if (opt.extensionalityResolution() != Options::ExtensionalityResolution::OFF) {
    _extensionality = new ExtensionalityClauseContainer(opt);
    //_active->addedEvent.subscribe(_extensionality, &ExtensionalityClauseContainer::addIfExtensionality);
  }
  else {
    _extensionality = 0;
  }

  s_instance = this;
}

/**
 * Destroy the SaturationAlgorithm object
 */
SaturationAlgorithm::~SaturationAlgorithm()
{
  ASS_EQ(s_instance,this);

  s_instance = 0;

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
  return _completeOptionSettings && !env.statistics->inferencesSkippedDueToColors
        && !env.statistics->discardedNonRedundantClauses; // this covers removals from LRS!
}

ClauseIterator SaturationAlgorithm::activeClauses()
{
  return _active->clauses();
}

/**
 * A function that is called when a clause is added to the active clause container.
 */
void SaturationAlgorithm::onActiveAdded(Clause* c)
{
  if (env.options->showActive()) {
    std::cout << "[SA] active: " << c->toString() << std::endl;
    // _neuralModel->printStats();
  }
}

/**
 * A function that is called when a clause is removed from the active clause container.
 */
void SaturationAlgorithm::onActiveRemoved(Clause* c)
{
  ASS(c->store()==Clause::ACTIVE);
  c->setStore(Clause::NONE);
  // at this point the c object may be deleted
}

void SaturationAlgorithm::onAllProcessed()
{
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

void SaturationAlgorithm::showClauseLiterals(Clause* c) {
  vector<int64_t> lits;
  for (Literal* lit : c->iterLits()) {
    // using negative indices for literals (otherwise might overlap with term ids!)
    int64_t litId = -1-(int64_t)lit->getId();
    lits.push_back(litId);

    if (_literalsShown.find(lit->getId())) // and having a dedicated DHSet form them
      continue;

    vector<int64_t> args;
    for (unsigned n = 0; n < lit->arity(); n++) {
      TermList arg = *lit->nthArgument(n);
      if (arg.isTerm()) {
        showSubterms(arg.term());
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
    std::cout << "[SA] passive: " << c->toString() << std::endl;
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
  if (_neuralActivityRecoring) {
    _neuralModel->journal(NeuralClauseEvaluationModel::JOURNAL_REM,c);
  }

  ASS(c->store()==Clause::PASSIVE);
  c->setStore(Clause::NONE);
  // at this point the c object can be deleted
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
 * A function that is called whenever a possibly new clause appears.
 */
void SaturationAlgorithm::onNewClause(Clause* cl)
{
  if (_splitter) {
    _splitter->onNewClause(cl);
  }

  if (env.options->showNew()) {
    std::cout << "[SA] new: " << cl->toString() << std::endl;
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
  ASS(c->isPropositional());

  if (env.options->showNewPropositional()) {
    std::cout << "[SA] new propositional: " << c->toString() << std::endl;
  }

  if (_consFinder) {
    _consFinder->onNewPropositionalClause(c);
  }
  if (_labelFinder) {
    _labelFinder->onNewPropositionalClause(c);
  }
}

/**
 * Called when a clause successfully passes the forward simplification
 */
void SaturationAlgorithm::onClauseRetained(Clause* cl)
{
  //cout << "[SA] retained " << cl->toString() << endl;

}

/**
 * Called whenever a clause is simplified or deleted at any point of the
 * saturation algorithm
 */
void SaturationAlgorithm::onClauseReduction(Clause* cl, Clause **replacements, unsigned numOfReplacements,
                                            Clause* premise, bool forward)
{
  ASS(cl);

  ClauseIterator premises;

  if (premise) {
    premises = pvi(getSingletonIterator(premise));
  }
  else {
    premises = ClauseIterator::getEmpty();
  }

  onClauseReduction(cl, replacements, numOfReplacements, premises, forward);
}

void SaturationAlgorithm::onClauseReduction(Clause* cl, Clause **replacements, unsigned numOfReplacements,
                                            ClauseIterator premises, bool forward)
{
  ASS(cl);

  static ClauseStack premStack;
  premStack.reset();
  premStack.loadFromIterator(premises);

  Clause *replacement = numOfReplacements ? *replacements : 0;

  if (env.options->showReductions()) {
    std::cout << "[SA] " << (forward ? "forward" : "backward") << " reduce: " << cl->toString() << endl;
    for(unsigned i = 0; i < numOfReplacements; i++){
      Clause* replacement = *replacements;
      if(replacement){ std::cout << "      replaced by " << replacement->toString() << endl; }
      replacements++;
    }
    ClauseStack::Iterator pit(premStack);
    while(pit.hasNext()){
      Clause* premise = pit.next();
      if(premise){ std::cout << "     using " << premise->toString() << endl; }
    }
  }

  if (_splitter) {
    _splitter->onClauseReduction(cl, pvi(ClauseStack::Iterator(premStack)), replacement);
  }

  if (replacement) {
    // Where an inference has multiple conclusions, onParenthood will only be run
    // for the final conclusion. This is unsafe when running with symbol elimination.
    // At the moment the only simplification rules that have multiple conclusions
    // are higher-order and it is assumed that we will not run higher-order along
    // with symbol elimination.
    // In the future if a first-order simplification rule is added with multiple
    // conclusions, this code should be updated.
    onParenthood(replacement, cl);
    while (premStack.isNonEmpty()) {
      onParenthood(replacement, premStack.pop());
    }
  }
}

void SaturationAlgorithm::onNonRedundantClause(Clause* c)
{
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
void SaturationAlgorithm::onParenthood(Clause* cl, Clause *parent)
{
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
  onActiveRemoved(cl);
}

/**
 * This function is subscribed to the remove event of the passive container
 * instead of the @b onPassiveRemoved function in the constructor, as the
 * @b onPassiveRemoved function is virtual.
 */
void SaturationAlgorithm::passiveRemovedHandler(Clause* cl)
{
  onPassiveRemoved(cl);
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
  ASS_LE(toNumber(cl->inputType()),toNumber(UnitInputType::CLAIM)); // larger input types should not appear in proof search

  if (_symEl) {
    _symEl->onInputClause(cl);
  }

  bool sosForAxioms = _opt.sos() == Options::Sos::ON || _opt.sos() == Options::Sos::ALL;
  sosForAxioms = sosForAxioms && cl->inputType() == UnitInputType::AXIOM;

  bool sosForTheory = _opt.sos() == Options::Sos::THEORY && _opt.sosTheoryLimit() == 0;

  if (_opt.sineToAge()) {
    unsigned level = cl->getSineLevel();
    // cout << "Adding " << cl->toString() << " level " << level;
    if (level == UINT_MAX) {
      level = env.maxSineLevel - 1; // as the next available (unused) value
      // cout << " -> " << level;
    }
    // cout << endl;
    cl->adaptAgeFrom(level);
  }

  if (sosForAxioms || (cl->isPureTheoryDescendant() && sosForTheory)) {
    addInputSOSClause(cl);
  }
  else {
    addNewClause(cl);
  }

  if (_instantiation) {
    _instantiation->registerClause(cl);
  }

  env.statistics->initialClauses++;
}

/**
 * Return literal selector that is to be used for set-of-support clauses
 */
LiteralSelector& SaturationAlgorithm::getSosLiteralSelector()
{
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
  ASS_EQ(toNumber(cl->inputType()),toNumber(UnitInputType::AXIOM));

  // we add an extra reference until the clause is added to some container, so that
  // it won't get deleted during some code e.g. in the onNewClause handler
  cl->incRefCnt();

  onNewClause(cl);

simpl_start:

  Clause *simplCl = _immediateSimplifier->simplify(cl);
  if (simplCl != cl) {
    if (!simplCl) {
      onClauseReduction(cl, 0, 0, 0);
      goto fin;
    }

    simplCl->incRefCnt();
    cl->decRefCnt(); // now cl is referenced from simplCl, so after removing the extra reference, it won't be destroyed

    onNewClause(simplCl);
    onClauseReduction(cl, &simplCl, 1, 0);
    cl = simplCl;
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
  TIME_TRACE("gnn-eval");

  Timer::updateInstructionCount();
  long long gnn_start_instrs = Timer::elapsedInstructions();

  _numPreds = env.signature->predicates();
  _numFuncs = env.signature->functions();
  _numSorts = env.signature->typeCons();

  // these guy must survive (in memory) until the gnnPerform call
  torch::Tensor sort_features = torch::empty({_numSorts,3}, torch::kFloat32);
  torch::Tensor symbol_features = torch::empty({_numPreds+_numFuncs,11}, torch::kFloat32);

  // sorts
  {
    float* sort_features_ptr = sort_features.data_ptr<float>();

    for (unsigned t = 0; t < _numSorts; t++) {
      Signature::Symbol* symb = env.signature->getTypeCon(t);
      if (symb->arity() > 0) {
        USER_ERROR("GNN currently only supports monomorphic FOL.");
      }
      (*sort_features_ptr++) = env.signature->isPlainCon(t);
      (*sort_features_ptr++) = env.signature->isBoolCon(t);
      (*sort_features_ptr++) = env.signature->isArithCon(t);
      // cout << "sort: " << t << " " << env.signature->isPlainCon(t) << " " << env.signature->isBoolCon(t) << " " << env.signature->isArithCon(t) << " # " << symb->name() << endl;
    }

    _neuralModel->gnnNodeKind("sort",sort_features);
  }

  // symbols
  {
    float* symbol_features_ptr = symbol_features.data_ptr<float>();

    vector<int64_t> symb2sort_one; // the symbs
    vector<int64_t> symb2sort_two; // the sorts

    vector<int64_t> symb2symb_one; // the smaller in prec
    vector<int64_t> symb2symb_two; // the larger in prec

    auto add_arity_symbol_features = [&symbol_features_ptr](unsigned arity) {
      (*symbol_features_ptr++) = (arity > 0);
      (*symbol_features_ptr++) = (arity > 1);
      (*symbol_features_ptr++) = (arity > 2);
      (*symbol_features_ptr++) = (arity > 4);
      (*symbol_features_ptr++) = (arity > 8);
    };

    for (unsigned p = 0; p < _numPreds; p++) {
      Signature::Symbol* symb = env.signature->getPredicate(p);
      (*symbol_features_ptr++) = (unsigned)(p==0);   // isEquality
      (*symbol_features_ptr++) = 0;                  // isFunction symbol
      (*symbol_features_ptr++) = symb->introduced();
      (*symbol_features_ptr++) = symb->skolem();
      (*symbol_features_ptr++) = symb->interpretedNumber();
      (*symbol_features_ptr++) = 1; // function symbol (KBO) weight
      add_arity_symbol_features(symb->arity());

      //cout << "symb: " << p << " " << (unsigned)(p==0) << " 0 " << symb->introduced() << " " << symb->skolem()
      //    << " " << symb->interpretedNumber() << " " << symb->arity() << " # " << symb->name() << endl;
      // cout << "symb-to-sort: " << p << " " << env.signature->getBoolSort() << endl;
      symb2sort_one.push_back(p);
      symb2sort_two.push_back(env.signature->getBoolSort());
      // pred-to-sort: predId sortId (which is always 1 == $o)
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
    for (unsigned f = 0; f < _numFuncs; f++) {
      Signature::Symbol* symb = env.signature->getFunction(f);

      (*symbol_features_ptr++) = 0;                  // isEquality
      (*symbol_features_ptr++) = 1;                  // isFunction symbol
      (*symbol_features_ptr++) = symb->introduced();
      (*symbol_features_ptr++) = symb->skolem();
      (*symbol_features_ptr++) = symb->interpretedNumber();
      (*symbol_features_ptr++) = _ordering->functionSymbolWeight(f);
      add_arity_symbol_features(symb->arity());

      //cout << "symb: " << FUNC_TO_SYMB(f) << " 0 1 " << symb->introduced() << " " << symb->skolem()
      //    << " " << symb->interpretedNumber() << " " << symb->arity() << " # " << symb->name() << endl;
      // cout << "symb-to-sort: " << FUNC_TO_SYMB(f) << " " << symb->fnType()->result().term()->functor() << endl;
      symb2sort_one.push_back(funcToSymb(f));
      symb2sort_two.push_back(symb->fnType()->result().term()->functor());
      // func-to-sort: funcId sortId --- this is the output sort (input sorts can be inferred from arguments' output sorts)
    }
    {
      DArray<unsigned> functions;
      functions.initFromIterator(getRangeIterator(0u, _numFuncs), _numFuncs);
      _ordering->sortArrayByFunctionPrecedence(functions);
      unsigned jumpLen = 1;
      do {
        for (unsigned idx = jumpLen; idx < _numFuncs; idx += jumpLen) {
          // cout << "symb-prec-next: " << FUNC_TO_SYMB(functions[idx-jumpLen]) << " " << FUNC_TO_SYMB(functions[idx]) << endl;
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

  vector<float> clause_features;
  vector<float> term_features;
  vector<float> var_features;

  ClauseIterator toAdd = _prb.clauseIterator();
  unsigned clauseId = 0;  // zero-based, ever growing
  unsigned subtermId = 0; // zero-based, ever growing
  unsigned clVarId = 0;   // zero-based, ever growing, each clause has its own variable nodes
  DHMap<unsigned,unsigned> clauseVariables; // from clause variables (as TermList::var()) to global variables of the whole CNF (non shared)

  struct TermTodo {
    Term* trm;        // the term to iterate through
    unsigned id;      // its id (for reporting edges)
    OperatorType* ot; // trm's operator type (careful, can't be used for twoVarEquality)
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

  auto term_features_for_vars_and_weight_the_var_case = [&term_features]() {
    term_features.push_back(1.0);   // non-ground
    term_features.push_back(0.0);
    term_features.push_back(0.0);
    term_features.push_back(0.0);
    term_features.push_back(0.0);   // non-leaf
    term_features.push_back(0.0);
    term_features.push_back(0.0);
    term_features.push_back(0.0);
  };

  std::vector<int64_t> clauseNums;
  clauseNums.reserve(UnitList::length(_prb.units()));

  Stack<TermTodo> subterms;
  while (toAdd.hasNext()) {
    Clause* cl = toAdd.next();
    clauseNums.push_back(cl->number());
    clauseVariables.reset();
    unsigned clWeight = 0;
    for (Literal* lit : cl->iterLits()) {
      clWeight += lit->weight();

      cls2trm_one.push_back(clauseId);
      cls2trm_two.push_back(subtermId);
      // cout << "cls-trm: " << clauseId << " " << subtermId << endl;

      // each literal is a trm!
      term_features.push_back((lit->isPositive()) ? 1.0 : -1.0); // only non-zero for literals and encodes polarity
      term_features.push_back(0.0);                              // position under my parent (here the clause, but for literals positions don't matter)
      term_features_for_vars_and_weight(lit);
      // cout << "trm: " << subtermId << " " << ((lit->isPositive()) ? 1.0 : -1.0) << " " << 0.0 << " ... " << lit->toString() << endl;

      trm2symb_one.push_back(subtermId);
      trm2symb_two.push_back(lit->functor());
      // cout << "trm-symb: " << subtermId << " " << lit->functor() << endl;

      ASS(subterms.isEmpty());
      subterms.push({lit,subtermId++,env.signature->getPredicate(lit->functor())->predType()});
      while (subterms.isNonEmpty()) {
        TermTodo& top = subterms.top();

        if (top.idx < top.trm->arity()) {
          term_features.push_back(0.0);   // proper subterms are not literals
          if ((top.trm->isLiteral() && top.trm->functor() == 0) // our parent was = literal (order does not matter)
              || top.trm->arity() == 1) { // stick with 0.0 for this case too (to keep the features balanced around 0.0)
            term_features.push_back(0.0); // subterms of = not distinguishable by idx
          } else {
            term_features.push_back(static_cast<float>(top.idx)/(top.trm->arity()-1.0)); // interpolate idx between 0.0 and 1.0
          }
          TermList arg = *top.trm->nthArgument(top.idx);
          // cout << "trm: " << subtermId << " " << 0.0 << " " << term_features.back() << " ... " << arg.toString() << endl;
          // the rest of term_features will follow, depending on whether arg is a proper term or a var

          // will be only used, if we are a var
          unsigned varSrt = (top.trm->isTwoVarEquality() ? top.trm->twoVarEqSort() : top.ot->arg(top.idx)).term()->functor();
          top.idx++; // next time round, will look at the next argument or die

          trm2trm_one.push_back(top.id);
          trm2trm_two.push_back(subtermId);
          // cout << "trm-trm: " << top.id << " " << subtermId << endl;

          if (arg.isTerm()) {
            Term* t = arg.term();
            term_features_for_vars_and_weight(t);

            trm2symb_one.push_back(subtermId);
            trm2symb_two.push_back(funcToSymb(t->functor()));

            // cout << "trm-symb: " << subtermId << " " << FUNC_TO_SYMB(t->functor()) << endl;
            subterms.push({t,subtermId,env.signature->getFunction(t->functor())->fnType()});
            // don't touch top anymore (push could cause reallocatio)!
          } else {
            term_features_for_vars_and_weight_the_var_case();

            ASS(arg.isVar());
            unsigned var = arg.var();
            unsigned* normVar;
            if (clauseVariables.getValuePtr(var,normVar)) {
              *normVar = clVarId++;
              // cout << "var: " << *normVar << " " << clauseVariables.size()-1 << endl;
              var_features.push_back(clauseVariables.size()-1);
              // cls-var: clauseId varId
              // cout << "cls-var: " << clauseId << " " << *normVar << endl;       // a clause knows about its variables (and numbers them internally starting from 0)
              cls2var_one.push_back(clauseId);
              cls2var_two.push_back(*normVar);

              // cout << "var-srt: " << *normVar << " " << varSrt << endl;          // a variable knows about its sort
              var2srt_one.push_back(*normVar);
              var2srt_two.push_back(varSrt);
            }

            // cout << "trm-var: " << subtermId << " " << *normVar << endl; // this subterm is a variable
            trm2var_one.push_back(subtermId);
            trm2var_two.push_back(*normVar);
          }
          subtermId++;
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

  // also here we (paranoidly) assume that the script module might not take any ownershipe of these tensors ...
  auto clause_features_t = torch::tensor(clause_features,torch::TensorOptions().dtype(torch::kFloat32)).reshape({clauseId,10});
  auto term_features_t = torch::tensor(term_features,torch::TensorOptions().dtype(torch::kFloat32)).reshape({subtermId,10});
  auto var_features_t = torch::tensor(var_features,torch::TensorOptions().dtype(torch::kFloat32)).reshape({clVarId,1});
  // ... and so want to have them in scope until the gnnPerform call

  _neuralModel->gnnNodeKind("clause",clause_features_t);
  _neuralModel->gnnNodeKind("term",term_features_t);
  _neuralModel->gnnNodeKind("var",var_features_t);

  _neuralModel->gnnEdgeKind("clause","term",cls2trm_one,cls2trm_two);
  _neuralModel->gnnEdgeKind("term","term",trm2trm_one,trm2trm_two);      // the sub-term (down) edges
  _neuralModel->gnnEdgeKind("clause","var",cls2var_one,cls2var_two);
  _neuralModel->gnnEdgeKind("var","sort",var2srt_one,var2srt_two);
  _neuralModel->gnnEdgeKind("term","var",trm2var_one,trm2var_two);       // some subterms are variables
  _neuralModel->gnnEdgeKind("term","symbol",trm2symb_one,trm2symb_two);  // and others are proper and thus have a symbol

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
  if (_neuralActivityRecoring || _neuralModelGuidance) {
    if (_neuralModel->useGage() || _neuralModel->useGweight()) {
      runGnnOnInput();
    }
  }

  ClauseIterator toAdd;
  if (env.options->randomTraversals()) {
    TIME_TRACE(TimeTrace::SHUFFLING);

    Stack<Clause *> aux;
    aux.loadFromIterator(_prb.clauseIterator());
    Shuffling::shuffleArray(aux,aux.size());
    toAdd = pvi(arrayIter(std::move(aux)));
  } else {
    toAdd = _prb.clauseIterator();
  }

  while (toAdd.hasNext()) {
    Clause* cl = toAdd.next();
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
}

Clause *SaturationAlgorithm::doImmediateSimplification(Clause* cl0)
{
  TIME_TRACE("immediate simplification");

  static bool sosTheoryLimit = _opt.sos() == Options::Sos::THEORY;
  static unsigned sosTheoryLimitAge = _opt.sosTheoryLimit();
  static ClauseStack repStack;
  repStack.reset();

  SplitSet *splitSet = 0;

  if (sosTheoryLimit && cl0->isPureTheoryDescendant() && cl0->age() > sosTheoryLimitAge) {
    return 0;
  }

  Clause* cl = cl0;

  Clause *simplCl = _immediateSimplifier->simplify(cl);
  if (simplCl != cl) {
    if (simplCl) {
      addNewClause(simplCl);
    }
    onClauseReduction(cl, &simplCl, 1, 0);
    return 0;
  }

  ClauseIterator cIt = _immediateSimplifier->simplifyMany(cl);
  if (cIt.hasNext()) {
    while (cIt.hasNext()) {
      Clause *simpedCl = cIt.next();
      if (!splitSet) {
        splitSet = simpedCl->splits();
      }
      else {
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
  if (env.options->randomTraversals()) {
    TIME_TRACE(TimeTrace::SHUFFLING);

    Shuffling::shuffle(cl);
  }

  // we increase the reference counter here so that the clause wouldn't
  // get destroyed during handling in the onNewClause handler
  //(there the control flow goes out of the SaturationAlgorithm class,
  // so we'd better not assume on what's happening out there)
  cl->incRefCnt();
  onNewClause(cl);
  _newClauses.push(cl);
  // we can decrease the counter here -- it won't get deleted because
  // the _newClauses RC stack already took over the clause
  cl->decRefCnt();
}

void SaturationAlgorithm::newClausesToUnprocessed()
{
  if (env.options->randomTraversals()) {
    TIME_TRACE(TimeTrace::SHUFFLING);

    Shuffling::shuffleArray(_newClauses.naked().begin(), _newClauses.size());
  }

  while (_newClauses.isNonEmpty()) {
    Clause* cl = _newClauses.popWithoutDec();
    switch (cl->store()) {
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
        // such clauses should not appear as new ones
        cout << cl->toString() << endl;
#endif
        ASSERTION_VIOLATION_REP(cl->store());
    }
    cl->decRefCnt(); // belongs to _newClauses.popWithoutDec()
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
  _generatedClauseCount++;
  env.statistics->generatedClauses++;

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
  ASS(cl->isEmpty());

  if (isRefutation(cl)) {
    onNonRedundantClause(cl);

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
  TIME_TRACE("forward simplification");

  if (env.options->lrsPreemptiveDeletes() && _passive->exceedsAllLimits(cl)) {
    RSTAT_CTR_INC("clauses discarded by limit in forward simplification");
    env.statistics->discardedNonRedundantClauses++;
    return false;
  }

  FwSimplList::Iterator fsit(_fwSimplifiers);

  while (fsit.hasNext()) {
    ForwardSimplificationEngine *fse = fsit.next();

    {
      Clause *replacement = 0;
      ClauseIterator premises = ClauseIterator::getEmpty();

      if (fse->perform(cl, replacement, premises)) {
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
    SimplificationEngine *se = sit.next();

    {
      ClauseIterator results = se->perform(cl);

      if (results.hasNext()) {
        while (results.hasNext()) {
          Clause *simpedCl = results.next();
          ASS(simpedCl != cl);
          repStack.push(simpedCl);
          addNewClause(simpedCl);
        }
        onClauseReduction(cl, repStack.begin(), repStack.size(), 0);
        return false;
      }
    }
  }

  bool synthesis = (env.options->questionAnswering() == Options::QuestionAnsweringMode::SYNTHESIS);

  if (synthesis) {
    ASS((_answerLiteralManager != nullptr));
    Clause* ansLitCl = cl;
    if (_splitter && cl->hasAnswerLiteral() && !cl->noSplits() && cl->computable()) {
      ansLitCl = _splitter->reintroduceAvatarAssertions(cl);
    }
    Clause* reduced = _answerLiteralManager->recordAnswerAndReduce(ansLitCl);
    if (reduced) {
      ansLitCl = reduced;
    }
    if (ansLitCl != cl) {
      addNewClause(ansLitCl);
      onClauseReduction(cl, &ansLitCl, 1, 0);
      return false;
    }
  }

  //TODO: hack that only clauses deleted by forward simplification can be destroyed (other destruction needs debugging)
  cl->incRefCnt();

  if (_splitter && !_opt.splitAtActivation()) {
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
  TIME_TRACE("backward simplification");

  BwSimplList::Iterator bsit(_bwSimplifiers);
  while (bsit.hasNext()) {
    BackwardSimplificationEngine *bse = bsit.next();

    BwSimplificationRecordIterator simplifications;
    bse->perform(cl, simplifications);
    while (simplifications.hasNext()) {
      BwSimplificationRecord srec = simplifications.next();
      Clause *redundant = srec.toRemove;
      ASS_NEQ(redundant, cl);

      Clause *replacement = srec.replacement;

      if (replacement) {
        addNewClause(replacement);
      }
      onClauseReduction(redundant, &replacement, 1, cl, false);

      // we must remove the redundant clause before adding its replacement,
      // as otherwise the redundant one might demodulate the replacement into
      // a tautology

      redundant->incRefCnt(); // we don't want the clause deleted before we record the simplification

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
  if (_clauseActivationInProgress) {
    // we cannot remove clause now, as there indexes might be traversed now,
    // and so we cannot modify them
    _postponedClauseRemovals.push(cl);
    return;
  }

  switch (cl->store()) {
    case Clause::PASSIVE: {
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
  // at this point the cl object can be already deleted
}

/**
 * Add clause @b c to the passive container
 */
void SaturationAlgorithm::addToPassive(Clause* cl)
{
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

  _clauseActivationInProgress = true;

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

  _conditionalRedundancyHandler->checkEquations(cl);

  auto generated = TIME_TRACE_EXPR(TimeTrace::CLAUSE_GENERATION, _generator->generateSimplify(cl));
  auto toAdd = TIME_TRACE_ITER(TimeTrace::CLAUSE_GENERATION, generated.clauses);

  while (toAdd.hasNext()) {
    Clause *genCl = toAdd.next();
    addNewClause(genCl);

    Inference::Iterator iit = genCl->inference().iterator();
    while (genCl->inference().hasNext(iit)) {
      Unit *premUnit = genCl->inference().next(iit);
      // Now we can get generated clauses having parents that are not clauses
      // Indeed, from induction we can have generated clauses whose parents do
      // not include the activated clause
      if (premUnit->isClause()) {
        Clause *premCl = static_cast<Clause *>(premUnit);
        onParenthood(genCl, premCl);
      }
    }
  }

  _clauseActivationInProgress = false;

  // now we remove clauses that could not be removed during the clause activation process
  if (env.options->randomTraversals()) {
    TIME_TRACE(TimeTrace::SHUFFLING);

    Shuffling::shuffleArray(_postponedClauseRemovals.begin(), _postponedClauseRemovals.size());
  }
  while (_postponedClauseRemovals.isNonEmpty()) {
    Clause* cl = _postponedClauseRemovals.pop();
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
  do {
    newClausesToUnprocessed();
    if (_neuralModelGuidance && _passive->limitsActive() && env.options->lrsPreemptiveDeletes()) {
      // so that we can start kicking out the really bad clauses already in forwardSimplify's exceedsAllLimits
      _neuralModel->bulkEval(*_unprocessed);
    }

    unsigned unprocessedPops = 0;
    while (!_unprocessed->isEmpty()) {
      unprocessedPops++;
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
      // It should not matter that much (from the point of view of the NN) that these new clauses are now unevaluated
      // (the assumption is that reduced good clause is also good)
    }

    afterUnprocessedLoop(unprocessedPops);

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
  init();
}

UnitList *SaturationAlgorithm::collectSaturatedSet()
{
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
  doUnprocessedLoop();

  if (_passive->isEmpty()) {
    MainLoopResult::TerminationReason termReason =
        isComplete() ? Statistics::SATISFIABLE : Statistics::REFUTATION_NOT_FOUND;
    MainLoopResult res(termReason);

    // if (termReason == Statistics::REFUTATION_NOT_FOUND){
    //   Shell::UIHelper::outputSaturatedSet(cout, pvi(UnitList::Iterator(collectSaturatedSet())));
    // }

    if (termReason == Statistics::SATISFIABLE && getOptions().proof() != Options::Proof::OFF) {
      res.saturatedSet = collectSaturatedSet();

      if (_splitter) {
        res.saturatedSet = _splitter->preprendCurrentlyAssumedComponentClauses(res.saturatedSet);
      }
    }
    throw MainLoopFinishedException(res);
  }

  /*
   * Only after processing the whole input (with the first call to doUnprocessedLoop)
   * it is time to recored for LRS the start time (and instrs) for the first iteration.
   */
  if (env.statistics->activations == 0) {
    _lrsStartTime = Timer::elapsedMilliseconds();
    _lrsStartInstrs = Timer::elapsedMegaInstructions();
  }

  Clause* cl = nullptr;
  {
    TIME_TRACE(TimeTrace::PASSIVE_CONTAINER_MAINTENANCE);
    cl = _passive->popSelected();
  }
  ASS_EQ(cl->store(), Clause::PASSIVE);
  cl->setStore(Clause::SELECTED);

  // we really want to do it here (it's explained "activations started" to the user)
  // and it should correspond to the number of times _passive->popSelected() was called (for good LRS estimates to work)
  env.statistics->activations++;

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
  // could be more precise, but we don't care too much
  unsigned startTime = Timer::elapsedDeciseconds();
  try {
    env.statistics->activations = 0;
    while (true) {
      doOneAlgorithmStep(); // will bump env.statistics->activations by one

      if (_activationLimit && env.statistics->activations > _activationLimit) {
        throw ActivationLimitExceededException();
      }
      if(_softTimeLimit && Timer::elapsedDeciseconds() - startTime > _softTimeLimit)
        throw TimeLimitExceededException();
    }
  }
  catch(const RefutationFoundException& r) {
    if (_neuralActivityRecoring) {
      Timer::disableLimitEnforcement();
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
  DHSet<Unit*> done; // will contain the processed proof units
  refutation->minimizeAncestorsAndUpdateSelectedStats(done);

  std::vector<int64_t> proof_units;
  auto it = done.iterator();
  while (it.hasNext()) {
    proof_units.push_back(it.next()->number());
  }
  _neuralModel->setProofUnitsAndSaveRecorded(proof_units,env.options->neuralActivityRecording());
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
void SaturationAlgorithm::setGeneratingInferenceEngine(SimplifyingGeneratingInference *generator)
{
  ASS(!_generator);
  _generator = generator;
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
void SaturationAlgorithm::setImmediateSimplificationEngine(ImmediateSimplificationEngine *immediateSimplifier)
{
  ASS(!_immediateSimplifier);
  _immediateSimplifier = immediateSimplifier;
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
void SaturationAlgorithm::addForwardSimplifierToFront(ForwardSimplificationEngine *fwSimplifier)
{
  FwSimplList::push(fwSimplifier, _fwSimplifiers);
  fwSimplifier->attach(this);
}

void SaturationAlgorithm::addSimplifierToFront(SimplificationEngine *simplifier)
{
  SimplList::push(simplifier, _simplifiers);
  simplifier->attach(this);
}

/**
 * Add a backward simplifier, so that it is applied before the
 * simplifiers that were added before it. The object takes ownership
 * of the backward simplifier and will take care of destroying it.
 */
void SaturationAlgorithm::addBackwardSimplifierToFront(BackwardSimplificationEngine *bwSimplifier)
{
  BwSimplList::push(bwSimplifier, _bwSimplifiers);
  bwSimplifier->attach(this);
}

/**
 * @since 05/05/2013 Manchester, splitting changed to new values
 * @author Andrei Voronkov
 */
SaturationAlgorithm *SaturationAlgorithm::createFromOptions(Problem& prb, const Options& opt, IndexManager *indexMgr)
{
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

  if (opt.splitting()) {
    res->_splitter = new Splitter();
  }

  // create generating inference engine
  CompositeGIE *gie = new CompositeGIE();

  if(opt.functionDefinitionIntroduction()) {
    gie->addFront(new DefinitionIntroduction);
  }

  //TODO here induction is last, is that right?
  if(opt.induction()!=Options::Induction::NONE){
    gie->addFront(new Induction());
  }

  if (opt.instantiation() != Options::Instantiation::OFF) {
    res->_instantiation = new Instantiation();
    // res->_instantiation->init();
    gie->addFront(res->_instantiation);
  }

  if (prb.hasEquality()) {
    gie->addFront(new EqualityFactoring());
    gie->addFront(new EqualityResolution());
    if (env.options->superposition()) {
      gie->addFront(new Superposition());
    }
  }
  else if (opt.unificationWithAbstraction() != Options::UnificationWithAbstraction::OFF) {
    gie->addFront(new EqualityResolution());
  }

  if (opt.combinatorySup()) {
    gie->addFront(new ArgCong());
    gie->addFront(new NegativeExt()); // TODO add option
    if (opt.narrow() != Options::Narrow::OFF) {
      gie->addFront(new Narrow());
    }
    if (!opt.pragmatic()) {
      gie->addFront(new SubVarSup());
    }
  }

  if(prb.hasFOOL() &&
    prb.isHigherOrder() && env.options->booleanEqTrick()){
  //  gie->addFront(new ProxyElimination::NOTRemovalGIE());
    gie->addFront(new BoolEqToDiseq());
  }

  if(opt.complexBooleanReasoning() && prb.hasBoolVar() &&
     prb.isHigherOrder() && !opt.lambdaFreeHol()){
    gie->addFront(new PrimitiveInstantiation()); //TODO only add in some cases
    gie->addFront(new ElimLeibniz());
  }

  if (env.options->choiceReasoning()) {
    gie->addFront(new Choice());
  }

  gie->addFront(new Factoring());
  if (opt.binaryResolution()) {
    gie->addFront(new BinaryResolution());
  }
  if (opt.unitResultingResolution() != Options::URResolution::OFF) {
    gie->addFront(new URResolution(opt.unitResultingResolution() == Options::URResolution::FULL));
  }
  if (opt.extensionalityResolution() != Options::ExtensionalityResolution::OFF) {
    gie->addFront(new ExtensionalityResolution());
  }
  if (opt.FOOLParamodulation()) {
    gie->addFront(new FOOLParamodulation());
  }
  if (opt.cases() && prb.hasFOOL() && !opt.casesSimp()) {
    gie->addFront(new Cases());
  }

  if((prb.hasLogicalProxy() || prb.hasBoolVar() || prb.hasFOOL()) &&
      prb.isHigherOrder() && !prb.quantifiesOverPolymorphicVar()){
    if(env.options->cnfOnTheFly() != Options::CNFOnTheFly::EAGER &&
       env.options->cnfOnTheFly() != Options::CNFOnTheFly::OFF){
      gie->addFront(new LazyClausificationGIE());
    }
  }

  if (opt.injectivityReasoning()) {
    gie->addFront(new Injectivity());
  }
  if (prb.hasEquality() && env.signature->hasTermAlgebras()) {
    if (opt.termAlgebraCyclicityCheck() == Options::TACyclicityCheck::RULE) {
      gie->addFront(new AcyclicityGIE());
    }
    else if (opt.termAlgebraCyclicityCheck() == Options::TACyclicityCheck::RULELIGHT) {
      gie->addFront(new AcyclicityGIE1());
    }
    if (opt.termAlgebraInferences()) {
      gie->addFront(new InjectivityGIE());
    }
  }
  if (env.options->functionDefinitionRewriting()) {
    gie->addFront(new FunctionDefinitionRewriting());
    res->addForwardSimplifierToFront(new FunctionDefinitionDemodulation());
  }

  CompositeSGI *sgi = new CompositeSGI();
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
    for (auto gen : allArithmeticSubtermGeneralizations()) {
      sgi->push(gen);
    }
  }

#if VZ3
  if (opt.theoryInstAndSimp() != Shell::Options::TheoryInstSimp::OFF) {
    sgi->push(new TheoryInstAndSimp());
  }
#endif

  res->setGeneratingInferenceEngine(sgi);

  res->setImmediateSimplificationEngine(createISE(prb, opt, res->getOrdering()));

  // create simplification engine

  if((prb.hasLogicalProxy() || prb.hasBoolVar() || prb.hasFOOL()) &&
      prb.isHigherOrder() && !prb.quantifiesOverPolymorphicVar()){
    if(env.options->cnfOnTheFly() != Options::CNFOnTheFly::EAGER &&
       env.options->cnfOnTheFly() != Options::CNFOnTheFly::OFF){
      res->addSimplifierToFront(new LazyClausification());
    }
  }

  // create forward simplification engine
  if (prb.hasEquality() && opt.innerRewriting()) {
    res->addForwardSimplifierToFront(new InnerRewriting());
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
      res->addForwardSimplifierToFront(new ForwardSubsumptionDemodulation(false));
    }
  }
  if (prb.hasEquality()) {
    switch (opt.forwardDemodulation()) {
      case Options::Demodulation::ALL:
      case Options::Demodulation::PREORDERED:
        if (opt.combinatorySup()) {
          res->addForwardSimplifierToFront(new ForwardDemodulationImpl<true>());
        }
        else {
          res->addForwardSimplifierToFront(new ForwardDemodulationImpl<false>());
        }
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
    if (opt.codeTreeSubsumption()) {
      res->addForwardSimplifierToFront(new CodeTreeForwardSubsumptionAndResolution(opt.forwardSubsumptionResolution()));
    } else {
      res->addForwardSimplifierToFront(new ForwardSubsumptionAndResolution(opt.forwardSubsumptionResolution()));
    }
  }
  else if (opt.forwardSubsumptionResolution()) {
    USER_ERROR("Forward subsumption resolution requires forward subsumption to be enabled.");
  }

  // create backward simplification engine
  if (prb.hasEquality()) {
    switch (opt.backwardDemodulation()) {
      case Options::Demodulation::ALL:
      case Options::Demodulation::PREORDERED:
        res->addBackwardSimplifierToFront(new BackwardDemodulation());
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
    res->addBackwardSimplifierToFront(new BackwardSubsumptionDemodulation());
  }

  bool backSubsumption = opt.backwardSubsumption() != Options::Subsumption::OFF;
  bool backSR = opt.backwardSubsumptionResolution() != Options::Subsumption::OFF;
  bool subsumptionUnitOnly = opt.backwardSubsumption() == Options::Subsumption::UNIT_ONLY;
  bool srUnitOnly = opt.backwardSubsumptionResolution() == Options::Subsumption::UNIT_ONLY;
  if (backSubsumption || backSR) {
    res->addBackwardSimplifierToFront(new BackwardSubsumptionAndResolution(backSubsumption, subsumptionUnitOnly, backSR, srUnitOnly));
  }

  if (opt.mode() == Options::Mode::CONSEQUENCE_ELIMINATION) {
    res->_consFinder = new ConsequenceFinder();
  }
  if (opt.showSymbolElimination()) {
    res->_symEl = new SymElOutput();
  }

  res->_conditionalRedundancyHandler.reset(ConditionalRedundancyHandler::create(opt, &ordering, res->_splitter));

  res->_answerLiteralManager = AnswerLiteralManager::getInstance(); // selects the right one, according to options!
  ASS(!res->_answerLiteralManager||opt.questionAnswering()!=Options::QuestionAnsweringMode::OFF);
  ASS( res->_answerLiteralManager||opt.questionAnswering()==Options::QuestionAnsweringMode::OFF);
  return res;
} // SaturationAlgorithm::createFromOptions

/**
 * Create local clause simplifier for problem @c prb according to options @c opt
 */
ImmediateSimplificationEngine *SaturationAlgorithm::createISE(Problem& prb, const Options& opt, Ordering& ordering)
{
  CompositeISE* res=new CompositeISE();

  if (prb.hasEquality() && opt.equationalTautologyRemoval()) {
    res->addFront(new EquationalTautologyRemoval());
  }

  switch (opt.condensation()) {
    case Options::Condensation::ON:
      res->addFront(new Condensation());
      break;
    case Options::Condensation::FAST:
      res->addFront(new FastCondensation());
      break;
    case Options::Condensation::OFF:
      break;
  }

  if (env.options->combinatorySup()) {
    res->addFront(new CombinatorDemodISE());
    res->addFront(new CombinatorNormalisationISE());
  }

  if (env.options->choiceReasoning()) {
    res->addFront(new ChoiceDefinitionISE());
  }

  if((prb.hasLogicalProxy() || prb.hasBoolVar() || prb.hasFOOL()) &&
      prb.isHigherOrder() && !env.options->addProxyAxioms()){
    if(env.options->cnfOnTheFly() == Options::CNFOnTheFly::EAGER){
      /*res->addFrontMany(new ProxyISE());
      res->addFront(new OrImpAndProxyISE());
      res->addFront(new NotProxyISE());
      res->addFront(new EqualsProxyISE());
      res->addFront(new PiSigmaProxyISE());*/
      res->addFrontMany(new EagerClausificationISE());
    }
    else {
      res->addFront(new IFFXORRewriterISE());
    }
    res->addFront(new BoolSimp());
  }

  if (prb.hasFOOL() && opt.casesSimp() && !opt.cases()) {
    res->addFrontMany(new CasesSimp());
  }

  // Only add if there are distinct groups
  if (prb.hasEquality() && env.signature->hasDistinctGroups()) {
    res->addFront(new DistinctEqualitySimplifier());
  }
  if (prb.hasEquality() && env.signature->hasTermAlgebras()) {
    if (opt.termAlgebraInferences()) {
      res->addFront(new DistinctnessISE());
      res->addFront(new InjectivityISE());
      res->addFront(new NegativeInjectivityISE());
    }
  }
  if (prb.hasInterpretedOperations() || prb.hasNumerals()) {
    if (env.options->arithmeticSubtermGeneralizations() == Options::ArithmeticSimplificationMode::FORCE) {
      for (auto gen : allArithmeticSubtermGeneralizations()) {
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
  if (prb.hasEquality()) {
    res->addFront(new TrivialInequalitiesRemovalISE());
  }
  res->addFront(new TautologyDeletionISE());
  if (env.options->newTautologyDel()) {
    res->addFront(new TautologyDeletionISE2());
  }
  res->addFront(new DuplicateLiteralRemovalISE());

  if (env.options->questionAnswering() == Options::QuestionAnsweringMode::PLAIN) {
    res->addFront(new AnswerLiteralResolver());
    if (env.options->questionAnsweringAvoidThese() != "") {
      res->addFront(new UndesiredAnswerLiteralRemoval(env.options->questionAnsweringAvoidThese()));
    }
  } else if (env.options->questionAnswering() == Options::QuestionAnsweringMode::SYNTHESIS) {
    res->addFront(new UncomputableAnswerLiteralRemoval());
    res->addFront(new MultipleAnswerLiteralRemoval());
  }
  return res;
}

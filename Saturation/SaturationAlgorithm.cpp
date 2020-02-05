
/*
 * File SaturationAlgorithm.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
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

#include "Inferences/InferenceEngine.hpp"
#include "Inferences/BackwardDemodulation.hpp"
#include "Inferences/BackwardSubsumptionResolution.hpp"
#include "Inferences/BinaryResolution.hpp"
#include "Inferences/CTFwSubsAndRes.hpp"
#include "Inferences/EqualityFactoring.hpp"
#include "Inferences/EqualityResolution.hpp"
#include "Inferences/ExtensionalityResolution.hpp"
#include "Inferences/FOOLParamodulation.hpp"
#include "Inferences/Factoring.hpp"
#include "Inferences/ForwardDemodulation.hpp"
#include "Inferences/ForwardLiteralRewriting.hpp"
#include "Inferences/ForwardSubsumptionAndResolution.hpp"
#include "Inferences/GlobalSubsumption.hpp"
#include "Inferences/HyperSuperposition.hpp"
#include "Inferences/InnerRewriting.hpp"
#include "Inferences/TermAlgebraReasoning.hpp"
#include "Inferences/SLQueryBackwardSubsumption.hpp"
#include "Inferences/Superposition.hpp"
#include "Inferences/URResolution.hpp"
#include "Inferences/Instantiation.hpp"
#include "Inferences/TheoryInstAndSimp.hpp"
#include "Inferences/Induction.hpp"

#include "Saturation/ExtensionalityClauseContainer.hpp"

#include "Shell/AnswerExtractor.hpp"
#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/UIHelper.hpp"

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

#include <math.h>

#define DEBUG_MODEL 0

#include <ATen/Parallel.h>

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

/**
 * Create a SaturationAlgorithm object
 *
 * The @b passiveContainer object will be used as a passive clause container, and
 * @b selector object to select literals before clauses are activated.
 */
SaturationAlgorithm::SaturationAlgorithm(Problem& prb, const Options& opt)
  : MainLoop(prb, opt),
    _clauseActivationInProgress(false),
    _fwSimplifiers(0), _bwSimplifiers(0), _splitter(0),
    _consFinder(0), _labelFinder(0), _symEl(0), _answerLiteralManager(0),
    _instantiation(0),
#if VZ3
    _theoryInstSimp(0),
#endif
    _generatedClauseCount(0),
    _activationLimit(0)
{
  CALL("SaturationAlgorithm::SaturationAlgorithm");
  ASS_EQ(s_instance, 0);  //there can be only one saturation algorithm at a time

  if (opt.evalForKarel()) { // load the models
    TimeCounter t(TC_DEEP_STUFF);

    // seems to be making this nicely single-threaded
    at::set_num_threads(1);
    
    _model = torch::jit::load(opt.evalForKarelPath().c_str());

    // cout << "Models loaded" << endl;
  }

  _activationLimit = opt.activationLimit();

  _ordering = OrderingSP(Ordering::create(prb, opt));
  if (!Ordering::trySetGlobalOrdering(_ordering)) {
    //this is not an error, it may just lead to lower performance (and most likely not significantly lower)
    cerr << "SaturationAlgorithm cannot set its ordering as global" << endl;
  }
  _selector = LiteralSelector::getSelector(*_ordering, opt, opt.selection());

  _completeOptionSettings = opt.complete(prb);

  _unprocessed = new UnprocessedClauseContainer();

  if (opt.useManualClauseSelection()){
    _passive = new ManCSPassiveClauseContainer(true, opt);
  } else {
    if (opt.useTheorySplitQueues()) {
      Lib::vvector<std::unique_ptr<PassiveClauseContainer>> queues;
      auto cutoffs = opt.theorySplitQueueCutoffs();
      for (unsigned i = 0; i < cutoffs.size(); i++)
      {
        auto name =  "Queue " + Int::toString(cutoffs[i]);
        queues.push_back(Lib::make_unique<AWPassiveClauseContainer>(false, opt, name));
      }

      _passive = new TheoryMultiSplitPassiveClauseContainer(true, opt, "", std::move(queues));
    } else {
      _passive = new AWPassiveClauseContainer(true, opt, "");
    }
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
  while (_bwSimplifiers) {
    BackwardSimplificationEngine* bse = BwSimplList::pop(_bwSimplifiers);
    bse->detach();
    delete bse;
  }

  delete _unprocessed;
  delete _active;
  delete _passive;
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

  LiteralIndexingStructure* gis=getIndexManager()->getGeneratingLiteralIndexingStructure();
  return pvi( getMappingIterator(gis->getAll(), SLQueryResult::ClauseExtractFn()) );
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

  /*
  if (_opt.showForKarel()) {
    cout << "pass: " << c->number() << "\n";
  }
  */

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

void SaturationAlgorithm::evaluate(Clause* cl, std::vector<torch::jit::IValue>& inputs)
{
  CALL("SaturationAlgorithm::evaluated");

  auto output = _model.forward(inputs).toTensor();
  float eval = output.item<float>();

#if DEBUG_MODEL
  cout << "evaluting: " << cl->number() << endl;
  cout << inputs[0] << endl;
  cout << eval << endl;
#endif

  cl->modelSaidYes = (eval <= 5.0);
  // cl->modelSaidYes = Random::getBit();
}

void SaturationAlgorithm::talkToKarel(Clause* cl, bool eval)
{
  CALL("SaturationAlgorithm::talkToKarel");

  ASS(_opt.showForKarel() || _opt.evalForKarel());

  if ((!_opt.showForKarel() || _shown.find(cl)) && // now reason to show
      (!eval || !_opt.evalForKarel() || _evaluated.find(cl))) { // now reason to evaluate
    return;
  }

  // pre-order traversal on parents:
  Inference* inf = cl->inference();
  inf->minimizePremises(); // this is here only formally, we don't look into avatar stuff (yet)
  unsigned parent_cnt = 0;
  Inference::Iterator iit = inf->iterator();
  while(inf->hasNext(iit)) {
    Unit* premUnit = inf->next(iit);
    talkToKarel(premUnit->asClause(),eval);
    parent_cnt++;
  }

  // parents known, now its time to report on this one

  // [2,cl_id,cl_age,cl_weight,cl_len,cl_numsplits,inf_id,parent_cl_id,parent_cl_id,...]
  if (_opt.showForKarel() && !_shown.find(cl)) {
    cout << "d: [2," << cl->number() << "," << cl->age() << "," << cl->weight() << "," << cl->size() << "," << (cl->splits() ? cl->splits()->size() : 0);
    cout << "," << inf->rule();
    Inference::Iterator iit = inf->iterator();
    while(inf->hasNext(iit)) {
      Unit* premUnit = inf->next(iit);
      cout << "," << premUnit->asClause()->number();
    }
    cout << "]\n";

    ALWAYS(_shown.insert(cl));
  }

  if (_opt.evalForKarel() && eval && !_evaluated.find(cl)) {
    TimeCounter t(TC_DEEP_STUFF);

    // [2,cl_id,cl_age,cl_weight,cl_len,cl_numsplits,inf_id,parent_cl_id,parent_cl_id,...]
    auto init_vec = torch::zeros({7+parent_cnt},torch::kInt64);

    init_vec[0] = 2;
    init_vec[1] = (int)cl->number();
    init_vec[2] = (int)cl->age();
    init_vec[3] = (int)cl->weight();
    init_vec[4] = (int)cl->size();
    init_vec[5] = (int)(cl->splits() ? cl->splits()->size() : 0);
    init_vec[6] = (int)inf->rule();
    unsigned idx = 7;
    Inference::Iterator iit = inf->iterator();
    while(inf->hasNext(iit)) {
      Unit* premUnit = inf->next(iit);
      init_vec[idx++] = (int) premUnit->asClause()->number();
    }
    std::vector<torch::jit::IValue> inputs;
    inputs.push_back(init_vec);

    evaluate(cl, inputs);

    ALWAYS(_evaluated.insert(cl));
  }
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
void SaturationAlgorithm::onClauseReduction(Clause* cl, Clause* replacement, Clause* premise, bool forward)
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

  onClauseReduction(cl, replacement, premises, forward);
}

void SaturationAlgorithm::onClauseReduction(Clause* cl, Clause* replacement,
    ClauseIterator premises, bool forward)
{
  CALL("SaturationAlgorithm::onClauseReduction/4");
  ASS(cl);

  static ClauseStack premStack;
  premStack.reset();
  premStack.loadFromIterator(premises);

  if (env.options->showReductions()) {
    env.beginOutput();
    env.out() << "[SA] " << (forward ? "forward" : "backward") << " reduce: " << cl->toString() << endl;
    if(replacement){ env.out() << "     replaced by " << replacement->toString() << endl; }
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
  ASS_LE(cl->inputType(),Clause::CLAIM); // larger input types should not appear in proof search

  cl->markInput();

  if (_symEl) {
    _symEl->onInputClause(cl);
  }

  bool sosForAxioms = _opt.sos() == Options::Sos::ON || _opt.sos() == Options::Sos::ALL; 
  sosForAxioms = sosForAxioms && cl->inputType()==Clause::AXIOM;

  unsigned isTheory = cl->inference()->isTheoryAxiom() ? static_cast<unsigned>(cl->inference()->rule()) : 0;
  bool sosForTheory = _opt.sos() == Options::Sos::THEORY && _opt.sosTheoryLimit() == 0;

  if (_opt.showForKarel()) {
    // [1,cl_id,cl_age,cl_weight,cl_len,isgoal,istheory,sine]

    cout << "i: [1," << cl->number() << "," << cl->age() << "," << cl->weight() << "," << cl->size();
    cout << "," << cl->isGoal() << "," << isTheory << "," << cl->getSineLevel() << "]\n";

    /*
    cout << "init: " << cl->number() << " isGoal: " << cl->isGoal() << " isTheory: " << isTheory
         << " SInE: " << cl->getSineLevel() << endl;
    */
    /*
    if (isTheory) {
      Formula* f = Formula::fromClause(cl);
      cout << "tax: " << cl->number() << " " << TPTPPrinter::toString(f) << endl;
     f->destroy();
    }
    */
    ALWAYS(_shown.insert(cl));
  }

  if (_opt.evalForKarel()) {
    TimeCounter t(TC_DEEP_STUFF);

    // [1,cl_id,cl_age,cl_weight,cl_len,isgoal,istheory,sine]
    static auto init_vec = torch::zeros({8},torch::kInt64);
    init_vec[0] = 1;
    init_vec[1] = (int)cl->number();
    init_vec[2] = (int)cl->age();
    init_vec[3] = (int)cl->weight();
    init_vec[4] = (int)cl->size();
    init_vec[5] = (int)cl->isGoal();
    init_vec[6] = (int)isTheory;
    init_vec[7] = (int)cl->getSineLevel();

    static std::vector<torch::jit::IValue> inputs;
    inputs.clear();
    inputs.push_back(init_vec);

    evaluate(cl,inputs);

    // TODO: store the output value
    ALWAYS(_evaluated.insert(cl));
  }


  if (_opt.sineToAge()) {
    unsigned level = cl->getSineLevel();
    // cout << "Adding " << cl->toString() << " level " << level;
    if (level == UINT_MAX) {
      level = env.maxClausePriority;
      // cout << " -> " << level;
    }
    // cout << endl;
    cl->setAge(level);
  }

  if (sosForAxioms || (cl->inference()->isTheoryAxiom() && sosForTheory)){
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
  ASS_EQ(cl->inputType(),Clause::AXIOM);

  //we add an extra reference until the clause is added to some container, so that
  //it won't get deleted during some code e.g. in the onNewClause handler
  cl->incRefCnt();

  onNewClause(cl);

simpl_start:

  Clause* simplCl=_immediateSimplifier->simplify(cl);
  if (simplCl != cl) {
    if (!simplCl) {
      onClauseReduction(cl, 0, 0);
      goto fin;
    }

    simplCl->incRefCnt();
    cl->decRefCnt(); //now cl is referenced from simplCl, so after removing the extra reference, it won't be destroyed

    onNewClause(simplCl);
    onClauseReduction(cl, simplCl, 0);
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


/**
 * Insert clauses of the problem into the SaturationAlgorithm object
 * and initialize some internal structures.
 */
void SaturationAlgorithm::init()
{
  CALL("SaturationAlgorithm::init");

  ClauseIterator toAdd = _prb.clauseIterator();

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
}

Clause* SaturationAlgorithm::doImmediateSimplification(Clause* cl0)
{
  CALL("SaturationAlgorithm::doImmediateSimplification");

  static bool sosTheoryLimit = _opt.sos()==Options::Sos::THEORY;
  static unsigned sosTheoryLimitDepth = _opt.sosTheoryLimit();

  if(sosTheoryLimit && cl0->isTheoryDescendant() && cl0->inference()->maxDepth() > sosTheoryLimitDepth){
    return 0;
  }

  Clause* cl=cl0;

  Clause* simplCl=_immediateSimplifier->simplify(cl);
  if (simplCl != cl) {
    if (simplCl) {
      addNewClause(simplCl);
    }
    onClauseReduction(cl, simplCl, 0);
    return 0;
  }

  if (cl != cl0 && cl0->isInput()) {
    //immediate simplifications maintain the state of a clause as input
    cl->markInput();
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

  //cout << "new clause: " << cl->toString() << endl;

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
#if VDEBUG
    case Clause::SELECTED:
    case Clause::ACTIVE:
      cout << "FAIL: " << cl->toString() << endl;
      //such clauses should not appear as new ones
      cout << cl->toString() << endl;
      ASSERTION_VIOLATION_REP(cl->store());
#endif
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

  if (_opt.showForKarel() || _opt.evalForKarel()) {
    talkToKarel(cl,false /* not necessary to evaluate this clause (at least not now) */ );
  }
  if (_opt.showForKarel()) {
    cout << "e: " << cl->number() << "\n";
  }

  if (isRefutation(cl)) {
    onNonRedundantClause(cl);

    if(cl->isTheoryDescendant() ){
      ASSERTION_VIOLATION_REP("A pure theory descendant is empty, which means theory axioms are inconsistent");
      reportSpiderFail();
      // this is a poor way of handling this in release mode but it prevents unsound proofs
      throw MainLoop::MainLoopFinishedException(Statistics::REFUTATION_NOT_FOUND);
    }
    if(cl->inputType() == Unit::AXIOM){
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
        onClauseReduction(cl, replacement, premises);

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
      onClauseReduction(redundant, replacement, cl, false);

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
    _passive->remove(cl);
    break;
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

  if (_opt.evalForKarel()) {
    talkToKarel(cl);
  }

  _passive->add(cl);
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
bool SaturationAlgorithm::activate(Clause* cl)
{
  CALL("SaturationAlgorithm::activate");

  if (_consFinder && _consFinder->isRedundant(cl)) {
    return false;
  }

  if (_splitter && _opt.splitAtActivation()) {
    if (_splitter->doSplitting(cl)) {
      return false;
    }
  }

  bool redundant=false;
  ClauseIterator instances = ClauseIterator::getEmpty();
#if VZ3
  if(_theoryInstSimp){
    instances = _theoryInstSimp->generateClauses(cl,redundant);
  }
#endif
  if(redundant){ 
    removeActiveOrPassiveClause(cl);
    return false; 
  }

  _clauseActivationInProgress=true;

  if (!cl->numSelected()) {
    TimeCounter tc(TC_LITERAL_SELECTION);

    _selector->select(cl);
  }

  ASS_EQ(cl->store(), Clause::SELECTED);
  cl->setStore(Clause::ACTIVE);
  env.statistics->activeClauses++;
  _active->add(cl);


    ClauseIterator toAdd= pvi(getConcatenatedIterator(instances,_generator->generateClauses(cl)));

    while (toAdd.hasNext()) {
      Clause* genCl=toAdd.next();

      addNewClause(genCl);

      Inference::Iterator iit=genCl->inference()->iterator();
      while (genCl->inference()->hasNext(iit)) {
        Unit* premUnit=genCl->inference()->next(iit);
        ASS(premUnit->isClause());
        Clause* premCl=static_cast<Clause*>(premUnit);

        onParenthood(genCl, premCl);
      }
    }

  _clauseActivationInProgress=false;


  //now we remove clauses that could not be removed during the clause activation process
  while (_postponedClauseRemovals.isNonEmpty()) {
    Clause* cl=_postponedClauseRemovals.pop();
    if (cl->store() != Clause::ACTIVE &&
	cl->store() != Clause::PASSIVE) {
      continue;
    }
    removeActiveOrPassiveClause(cl);
  }

  return true; 
}

/**
 * Perform the loop that puts clauses from the unprocessed to the passive container.
 */
void SaturationAlgorithm::doUnprocessedLoop()
{
  CALL("SaturationAlgorithm::doUnprocessedLoop");

start:

  newClausesToUnprocessed();

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
  onAllProcessed();
  if (!clausesFlushed()) {
    //there were some new clauses added, so let's process them
    goto start;
  }

}

void SaturationAlgorithm::handleUnsuccessfulActivation(Clause* cl)
{
  CALL("SaturationAlgorithm::handleUnsuccessfulActivation");

  //ASS_EQ(cl->store(), Clause::SELECTED);
  cl->setStore(Clause::NONE);
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

  LiteralIndexingStructure* gis=getIndexManager()->getGeneratingLiteralIndexingStructure();

  UnitList* res = 0;
  SLQueryResultIterator qrit = gis->getAll();
  while (qrit.hasNext()) {
    SLQueryResult qres = qrit.next();
    UnitList::push(qres.clause, res);
    qres.clause->incRefCnt();
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
        res.saturatedSet = _splitter->explicateAssertionsForSaturatedClauseSet(res.saturatedSet);
      }
    }
    throw MainLoopFinishedException(res);
  }

  Clause* cl = _passive->popSelected();
  ASS_EQ(cl->store(),Clause::PASSIVE);
  cl->setStore(Clause::SELECTED);

  if (_opt.showForKarel()) {
    talkToKarel(cl,false /* just report, if not done yet (evaluation must have taken place before putting into passive)*/);
  }
  if (_opt.showForKarel()) {
    cout << "s: " << cl->number() << "\n";
  }

  if (!handleClauseBeforeActivation(cl)) {
    return;
  }

  bool isActivated=activate(cl);
  if (!isActivated) {
    handleUnsuccessfulActivation(cl);
  }
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
    }
  }
  catch(ThrowableBase&)
  {
    tryUpdateFinalClauseCount();
    throw;
  }

}

#if VZ3
void SaturationAlgorithm::setTheoryInstAndSimp(TheoryInstAndSimp* t)
{
  ASS(t);
  _theoryInstSimp=t;
  _theoryInstSimp->attach(this);
}
#endif

/**
 * Assign an generating inference object @b generator to be used
 *
 * This object takes ownership of the @b generator object
 * and will be responsible for its deletion.
 *
 * To use multiple generating inferences, use the @b CompositeGIE
 * object.
 */
void SaturationAlgorithm::setGeneratingInferenceEngine(GeneratingInferenceEngine* generator)
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

  if (prb.hasEquality()) {
    gie->addFront(new EqualityFactoring());
    gie->addFront(new EqualityResolution());
    gie->addFront(new Superposition());
  }
  else if(opt.unificationWithAbstraction()!=Options::UnificationWithAbstraction::OFF){
    gie->addFront(new EqualityResolution()); 
  }
  gie->addFront(new Factoring());
  if (opt.binaryResolution()) {
    gie->addFront(new BinaryResolution());
  }
  if (opt.unitResultingResolution() != Options::URResolution::OFF) {
    gie->addFront(new URResolution());
  }
  if (opt.extensionalityResolution() != Options::ExtensionalityResolution::OFF) {
    gie->addFront(new ExtensionalityResolution());
  }
  if (opt.FOOLParamodulation()) {
    gie->addFront(new FOOLParamodulation());
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
#if VZ3
  if (opt.theoryInstAndSimp() != Shell::Options::TheoryInstSimp::OFF){
    res->setTheoryInstAndSimp(new TheoryInstAndSimp());
    //gie->addFront(new TheoryInstAndSimp());
  }
#endif

  res->setGeneratingInferenceEngine(gie);

  res->setImmediateSimplificationEngine(createISE(prb, opt));

  // create forward simplification engine
  if (prb.hasEquality() && opt.innerRewriting()) {
    res->addForwardSimplifierToFront(new InnerRewriting());
  }
  if (opt.hyperSuperposition()) {
    res->addForwardSimplifierToFront(new HyperSuperposition());
  }
  if (opt.globalSubsumption()) {
    res->addForwardSimplifierToFront(new GlobalSubsumption(opt));
  }
  if (opt.forwardLiteralRewriting()) {
    res->addForwardSimplifierToFront(new ForwardLiteralRewriting());
  }
  if (prb.hasEquality()) {
    switch(opt.forwardDemodulation()) {
    case Options::Demodulation::ALL:
    case Options::Demodulation::PREORDERED:
      res->addForwardSimplifierToFront(new ForwardDemodulation());
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
    if (opt.forwardSubsumptionResolution()) {
      //res->addForwardSimplifierToFront(new CTFwSubsAndRes(true));
      res->addForwardSimplifierToFront(new ForwardSubsumptionAndResolution(true));
    }
    else {
      //res->addForwardSimplifierToFront(new CTFwSubsAndRes(false));
      res->addForwardSimplifierToFront(new ForwardSubsumptionAndResolution(false));
    }
  }
  else if (opt.forwardSubsumptionResolution()) {
    USER_ERROR("Forward subsumption resolution requires forward subsumption to be enabled.");
  }

  // create backward simplification engine
  if (prb.hasEquality()) {
    switch(opt.backwardDemodulation()) {
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

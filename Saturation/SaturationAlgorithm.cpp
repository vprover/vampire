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

#include "Indexing/LiteralIndexingStructure.hpp"

#include "Inferences/BDDMarkingSubsumption.hpp"

#include "Kernel/BDD.hpp"
#include "Kernel/BDDConjunction.hpp"
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
#include "Inferences/BDDMarkingSubsumption.hpp"
#include "Inferences/BinaryResolution.hpp"
#include "Inferences/CTFwSubsAndRes.hpp"
#include "Inferences/EqualityFactoring.hpp"
#include "Inferences/EqualityResolution.hpp"
#include "Inferences/Factoring.hpp"
#include "Inferences/ForwardDemodulation.hpp"
#include "Inferences/ForwardLiteralRewriting.hpp"
#include "Inferences/ForwardSubsumptionAndResolution.hpp"
#include "Inferences/GlobalSubsumption.hpp"
#include "Inferences/HyperSuperposition.hpp"
#include "Inferences/InterpretedSimplifier.hpp"
#include "Inferences/RefutationSeekerFSE.hpp"
#include "Inferences/SLQueryForwardSubsumption.hpp"
#include "Inferences/SLQueryBackwardSubsumption.hpp"
#include "Inferences/Superposition.hpp"
#include "Inferences/URResolution.hpp"

#include "Shell/AnswerExtractor.hpp"
#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "SSplitter.hpp"

#include "ConsequenceFinder.hpp"
#include "Splitter.hpp"
#include "SymElOutput.hpp"
#include "SaturationAlgorithm.hpp"
#include "AWPassiveClauseContainer.hpp"
#include "Discount.hpp"
#include "LRS.hpp"
#include "Otter.hpp"

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
    _mergedBddEmptyClause(0),
    _limits(opt),
    _clauseActivationInProgress(false),
    _fwSimplifiers(0), _bwSimplifiers(0), _splitter(0),
    _propToBDDConv(this),
    _consFinder(0), _symEl(0), _bddMarkingSubsumption(0), _answerLiteralManager(0),
    _generatedClauseCount(0)
{
  CALL("SaturationAlgorithm::SaturationAlgorithm");
  ASS_EQ(s_instance, 0);  //there can be only one saturation algorithm at a time

  _ordering = OrderingSP(Ordering::create(prb, opt));
  if (!Ordering::trySetGlobalOrdering(_ordering)) {
    //this is not an error, it may just lead to lower performance (and most likely not significantly lower)
    cerr << "SaturationAlgorithm cannot set its ordering as global" << endl;
  }
  _selector = LiteralSelector::getSelector(*_ordering, opt, opt.selection());

  _propToBDD = false;
  _completeOptionSettings = opt.complete(prb);

  _unprocessed = new UnprocessedClauseContainer();
  _passive = new AWPassiveClauseContainer(opt);
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

  if (opt.maxWeight()) {
    _limits.setLimits(0,opt.maxWeight());
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
  if (_bddMarkingSubsumption) {
    delete _bddMarkingSubsumption;
  }

  _active->detach();
  _passive->detach();

  if (_generator) {
    _generator->detach();
  }
  if (_immediateSimplifier) {
    _immediateSimplifier->detach();
  }

  while(_fwSimplifiers) {
    ForwardSimplificationEngine* fse = FwSimplList::pop(_fwSimplifiers);
    fse->detach();
    delete fse;
  }
  while(_bwSimplifiers) {
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
  env.statistics->finalActiveClauses = inst->_active->size();
  env.statistics->finalPassiveClauses = inst->_passive->size();
}

/**
 * Return true if the run of the prover so far is complete
 */
bool SaturationAlgorithm::isComplete()
{
  return _completeOptionSettings;
}

ClauseIterator SaturationAlgorithm::activeClauses()
{
  CALL("SaturationAlgorithm::activeClauses");

  LiteralIndexingStructure* gis=getIndexManager()->getGeneratingLiteralIndexingStructure();
  return pvi( getMappingIterator(gis->getAll(), SLQueryResult::ClauseExtractFn()) );
}

ClauseIterator SaturationAlgorithm::passiveClauses()
{
  return _passive->iterator();
}

size_t SaturationAlgorithm::activeClauseCount()
{
  return _active->size();
}

size_t SaturationAlgorithm::passiveClauseCount()
{
  return _passive->size();
}


/**
 * A function that is called when a clause is added to the active clause container.
 */
void SaturationAlgorithm::onActiveAdded(Clause* c)
{
  LOG_UNIT("sa_active_added", c);
  LOG_INT("sa_active_size", _active->size());
}

/**
 * A function that is called when a clause is removed from the active clause container.
 */
void SaturationAlgorithm::onActiveRemoved(Clause* c)
{
  CALL("SaturationAlgorithm::onActiveRemoved");

  LOG_UNIT("sa_active_removed", c);
  LOG_INT("sa_active_size", _active->size());

  ASS(c->store()==Clause::ACTIVE || c->store()==Clause::REACTIVATED ||
      c->store()==Clause::SELECTED_REACTIVATED);

  if (c->store()==Clause::ACTIVE) {
    c->setStore(Clause::NONE);
    //at this point the c object may be deleted
  } else if (c->store()==Clause::REACTIVATED) {
    c->setStore(Clause::PASSIVE);
  } else if (c->store()==Clause::SELECTED_REACTIVATED) {
    c->setStore(Clause::SELECTED);
  }
#if VDEBUG
  else {
    ASSERTION_VIOLATION;
  }
#endif
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

  if (_bddMarkingSubsumption) {
    _bddMarkingSubsumption->onAllProcessed();
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
  LOG_UNIT("sa_passive_added", c);
  LOG_INT("sa_passive_size", _passive->size());

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

  LOG_UNIT("sa_passive_removed", c);
  LOG_INT("sa_passive_size", _passive->size());

  ASS(c->store()==Clause::PASSIVE || c->store()==Clause::REACTIVATED)

  if (c->store()==Clause::PASSIVE) {
    c->setStore(Clause::NONE);
    //at this point the c object can be deleted
  } else if (c->store()==Clause::REACTIVATED) {
    c->setStore(Clause::ACTIVE);
  }
#if VDEBUG
  else {
    ASSERTION_VIOLATION;
  }
#endif
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
  LOG_UNIT("sa_passive_selected", c);
  LOG_INT("sa_passive_size", _passive->size());
}

/**
 * A function that is called when a clause is added to the unprocessed clause container.
 */
void SaturationAlgorithm::onUnprocessedAdded(Clause* c)
{
  LOG_UNIT("sa_unprocessed_added", c);
}

/**
 * A function that is called when a clause is removed from the unprocessed clause container.
 */
void SaturationAlgorithm::onUnprocessedRemoved(Clause* c)
{
  LOG_UNIT("sa_unprocessed_removed", c);
}

void SaturationAlgorithm::onUnprocessedSelected(Clause* c)
{
  LOG_UNIT("sa_unprocessed_selected", c);
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

  if (!cl->prop()) {
    BDD* bdd=BDD::instance();
    BDDNode* prop=bdd->getFalse();

    Inference* inf=cl->inference();
    Inference::Iterator it=inf->iterator();
    while(inf->hasNext(it)) {
      Unit* premu=inf->next(it);
      if (!premu->isClause()) {
	//the premise comes from preprocessing
	continue;
      }
      Clause* prem=static_cast<Clause*>(premu);
      if (!prem->prop()) {
	//the premise comes from preprocessing
	continue;
      }

      prop=bdd->disjunction(prop, prem->prop());
    }

    cl->initProp(prop);
    if (!bdd->isTrue(prop)) {
      InferenceStore::instance()->recordNonPropInference(cl);
    }
  }

  LOG_UNIT("sa_new_clause", cl);

  if (!_propToBDD && cl->isPropositional()) {
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

  LOG_UNIT("sa_new_prop_clause", c);

  if (_bddMarkingSubsumption) {
    _bddMarkingSubsumption->onNewPropositionalClause(c);
  }

  if (_consFinder) {
    _consFinder->onNewPropositionalClause(c);
  }
}

/**
 * Called when a clause successfully passes the forward simplification
 */
void SaturationAlgorithm::onClauseRetained(Clause* cl)
{
  CALL("SaturationAlgorithm::onClauseRetained");

  LOG_UNIT("sa_retained_clause", cl);
}

/**
 * Called whenever a clause is simplified or deleted at any point of the
 * saturation algorithm
 *
 * In case the deletion of clause @b cl is justified also by some other clause than
 * @b replacement and @b premise clauses, it should be passed as the @b reductionPremise.
 * Otherwise the @b reductionPremise should be 0.
 */
void SaturationAlgorithm::onClauseReduction(Clause* cl, Clause* replacement,
    Clause* premise, Clause* reductionPremise, bool forward)
{
  CALL("SaturationAlgorithm::onClauseReduction/5");
  ASS(cl);

  ClauseIterator premises;
  
  if (reductionPremise) {
    ASS(premise);
    premises = pvi( getConcatenatedIterator(getSingletonIterator(premise), getSingletonIterator(reductionPremise)) );
  }
  else if (premise) {
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

  if (replacement && BDD::instance()->isTrue(replacement->prop())) {
    //clause was rewritten into tautology, so we look at it as if
    //it was just deleted
    replacement=0;
  }

  static ClauseStack premStack;
  premStack.reset();
  premStack.loadFromIterator(premises);

  if (_splitter) {
    _splitter->onClauseReduction(cl, pvi( ClauseStack::Iterator(premStack) ), replacement);
  }

  if (replacement) {
    onParenthood(replacement, cl);
    while(premStack.isNonEmpty()) {
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
  ASS_EQ(cl->prop(),0);

  cl->markInput();
  cl->initProp(BDD::instance()->getFalse());

  if (_symEl) {
    _symEl->onInputClause(cl);
  }

  if (_propToBDD) {
    //put propositional predicates into BDD part
    cl=_propToBDDConv.simplify(cl);
    if (!cl) {
      return;
    }
  }

  if (_opt.sos() != Options::SOS_OFF && cl->inputType()==Clause::AXIOM) {
    addInputSOSClause(cl);
  } else {
    addNewClause(cl);
  }

  env.statistics->initialClauses++;
}

/**
 * Return literal selector that is to be used for set-of-support clauses
 */
LiteralSelector& SaturationAlgorithm::getSosLiteralSelector()
{
  CALL("SaturationAlgorithm::getSosLiteralSelector");

  if (_opt.sos() == Options::SOS_ALL) {
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
  if (simplCl!=cl) {
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

  ASS(!cl->selected());
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

  while(toAdd.hasNext()) {
    Clause* cl=toAdd.next();
    addInputClause(cl);
  }

  _sharing.init(this);
  if (_splitter) {
    _splitter->init(this);
  }
  if (_consFinder) {
    _consFinder->init(this);
  }
  if (_symEl) {
    _symEl->init(this);
  }
  if (_bddMarkingSubsumption) {
    _bddMarkingSubsumption->init(this);
  }

  _startTime=env.timer->elapsedMilliseconds();
}

/**
 * Class of @b ForwardSimplificationPerformer objects that
 * perform the forward simplification only if it leads to
 * deletion of the clause being simplified. (Other
 * possibility would be to also perform simplifications that
 * only alter the propositional part of simplified clause,
 * not delete it.)
 */
class SaturationAlgorithm::TotalSimplificationPerformer
: public ForwardSimplificationPerformer
{
public:
  TotalSimplificationPerformer(SaturationAlgorithm* sa, Clause* cl) : _sa(sa), _cl(cl) {}

  void perform(ClauseIterator premises, Clause* replacement)
  {
    CALL("TotalSimplificationPerformer::perform");
    ASS(_cl);

    BDD* bdd=BDD::instance();

    BDDNode* oldClProp=_cl->prop();

    LOG_UNIT("sa_fw_simpl_red_clause",_cl);
    TRACE("sa_fw_simpl",
	tout << "->>--------\n";
	ClauseList* lst=0;
	while(premises.hasNext()) {
	  Clause* premise=premises.next();
	  ASS(willPerform(premise));
	  ClauseList::push(premise, lst);
	  tout << ":" << (*premise) << endl;
	}
	cout << "-" << (*_cl) << endl;
	premises=pvi( ClauseList::DestructiveIterator(lst) );
    );

    if (replacement) {
      replacement->initProp(oldClProp);
      InferenceStore::instance()->recordNonPropInference(replacement);
      _sa->addNewClause(replacement);
    }
    _sa->onClauseReduction(_cl, replacement, premises);

    _cl->setProp(bdd->getTrue());
    InferenceStore::instance()->recordPropReduce(_cl, oldClProp, bdd->getTrue());
    _cl=0;

    TRACE("sa_fw_simpl",
	if (replacement) {
	  tout << "+" << (*replacement) << endl;
	}
	tout << "removed\n";
	tout << "^^^^^^^^^^^^\n";
    );
  }

  bool willPerform(Clause* premise)
  {
    CALL("TotalSimplificationPerformer::willPerform");
    ASS(_cl);

    if (!premise) {
      return true;
    }

    if ( !ColorHelper::compatible(_cl->color(), premise->color()) ) {
      return false;
    }

    BDD* bdd=BDD::instance();
    if (!bdd->isXOrNonYConstant(_cl->prop(), premise->prop(), true)) {
      return false;
    }
    return true;
  }

  bool clauseKept()
  { return _cl; }
private:
  SaturationAlgorithm* _sa;
  Clause* _cl;
};


Clause* SaturationAlgorithm::doImmediateSimplification(Clause* cl0)
{
  CALL("SaturationAlgorithm::doImmediateSimplification");
  ASS(cl0->prop());

  Clause* cl=cl0;

  Clause* simplCl=_immediateSimplifier->simplify(cl);
  if (simplCl!=cl) {
    if (simplCl) {
      addNewClause(simplCl);
    }
    onClauseReduction(cl, simplCl, 0);
    return 0;
  }

  if (cl!=cl0 && cl0->isInput()) {
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

  //we increase the reference counter here so that the clause wouldn't
  //get destroyed during handling in the onNewClause handler
  //(there the control flow goes out of the SaturationAlgorithm class,
  //so we'd better not assume on what's happening out there)
  cl->incRefCnt();

  if (_opt.abstraction() && cl->number()%100000==(24788+(env.statistics->inputClauses%50000)) && env.statistics->inputClauses%3==0) {
    Clause* newCl = 0;
    if (cl->length()>1) {
      LiteralStack lits;
      lits.loadFromIterator(Clause::Iterator(*cl));
      newCl = Clause::fromStack(lits, cl->inputType(), cl->inference());
    }
    else if (cl->length()==1) {
      Literal* lit = (*cl)[0];
      if (lit->arity()) {
	TermList orig = *lit->nthArgument(0);
	Literal* newLit = EqHelper::replace(lit, orig, TermList(lit->vars(), false));
	newCl = Clause::fromIterator(getSingletonIterator(newLit), cl->inputType(), cl->inference());
      }
    }
    if (newCl) {
      cl->incRefCnt();
      newCl->incRefCnt();
      cl=newCl;
    }
  }

  onNewClause(cl);

  ASS(cl->prop());

  _newClauses.push(cl);
  //we can decrease the counter here -- it won't get deleted because
  //the _newClauses RC stack already took over the clause
  cl->decRefCnt();
}

void SaturationAlgorithm::newClausesToUnprocessed()
{
  CALL("SaturationAlgorithm::newClausesToUnprocessed");

  while(_newClauses.isNonEmpty()) {
    Clause* cl=_newClauses.popWithoutDec();

    if (BDD::instance()->isTrue(cl->prop())) {
      continue;
    }

    switch(cl->store())
    {
    case Clause::BACKTRACKED:
    case Clause::UNPROCESSED:
      break;
    case Clause::PASSIVE:
    case Clause::REACTIVATED:
      onNonRedundantClause(cl);
      break;
    case Clause::ACTIVE:
      ASS(!cl->isEmpty());
      reanimate(cl);
      break;
    case Clause::NONE:
      addUnprocessedClause(cl);
      break;
#if VDEBUG
    case Clause::SELECTED:
    case Clause::SELECTED_REACTIVATED:
      //such clauses should not appear as new ones
      ASSERTION_VIOLATION;
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
  ASS(cl->prop());

  _generatedClauseCount++;
  env.statistics->generatedClauses++;

  BDD* bdd=BDD::instance();
  ASS(!bdd->isTrue(cl->prop()));

  env.checkTimeSometime<64>();

  if (_bddMarkingSubsumption && _bddMarkingSubsumption->subsumed(cl)) {
    return;
  }

  cl=doImmediateSimplification(cl);
  if (!cl) {
    return;
  }
  ASS(!bdd->isTrue(cl->prop()));

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
    throw RefutationFoundException(cl);
  }

  if (_splitter && _splitter->handleEmptyClause(cl)) {
    return;
  }

  BDD* bdd=BDD::instance();

  ASS(!bdd->isFalse(cl->prop()));
  env.statistics->bddPropClauses++;

  if (_mergedBddEmptyClause==0) {
    cl->incRefCnt();
    onNonRedundantClause(cl);
    _mergedBddEmptyClause=cl;
    onNewUsefulPropositionalClause(cl);
    return;
  }
  BDDNode* newProp=bdd->conjunction(_mergedBddEmptyClause->prop(), cl->prop());
  if (newProp!=_mergedBddEmptyClause->prop()) {
    onNonRedundantClause(cl);
    onNewUsefulPropositionalClause(cl);
  }
  if (bdd->isFalse(newProp)) {
    InferenceStore::instance()->recordMerge(cl, cl->prop(), _mergedBddEmptyClause, newProp);
    cl->setProp(newProp);
    onNonRedundantClause(cl);
    onNewUsefulPropositionalClause(cl);
    throw RefutationFoundException(cl);
  }
  if (newProp!=_mergedBddEmptyClause->prop()) {
    InferenceStore::instance()->recordMerge(_mergedBddEmptyClause, _mergedBddEmptyClause->prop(), cl, newProp);
    _mergedBddEmptyClause->setProp(newProp);
    onNonRedundantClause(_mergedBddEmptyClause);
    return;
  }
}

/**
 * Reanimace clause @b cl
 *
 * Reanimation of a clause means that an active clause is put into
 * the passive container, so that it will be used once again for
 * generating inferences. In the meantime the clause still remains
 * also in the active container, so that we save on index updates.
 */
void SaturationAlgorithm::reanimate(Clause* cl)
{
  CALL("SaturationAlgorithm::reanimate");
  ASS_EQ(cl->store(), Clause::ACTIVE);

  ASS(!BDD::instance()->isTrue(cl->prop()));

  cl->setStore(Clause::REACTIVATED);
  _passive->add(cl);
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

  if (cl->store()==Clause::REACTIVATED || cl->store()==Clause::SELECTED_REACTIVATED) {
    return true;
  }

  if (!getLimits()->fulfillsLimits(cl)) {
    RSTAT_CTR_INC("clauses discarded by weight limit in forward simplification");
    env.statistics->discardedNonRedundantClauses++;
    return false;
  }

  TotalSimplificationPerformer performer(this, cl);

  FwSimplList::Iterator fsit(_fwSimplifiers);

  while(fsit.hasNext()) {
    ForwardSimplificationEngine* fse=fsit.next();

    fse->perform(cl, &performer);
    if (!performer.clauseKept()) {
      break;
    }
  }

  //TODO: hack that only clauses deleted by forward simplification can be destroyed (other destruction needs debugging)
  if (performer.clauseKept()) {
    cl->incRefCnt();
  }

  if (!performer.clauseKept()) {
    return false;
  }


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

  BDD* bdd=BDD::instance();

  BwSimplList::Iterator bsit(_bwSimplifiers);
  while(bsit.hasNext()) {
    BackwardSimplificationEngine* bse=bsit.next();

    BwSimplificationRecordIterator simplifications;
    bse->perform(cl,simplifications);
    while(simplifications.hasNext()) {
      BwSimplificationRecord srec=simplifications.next();
      Clause* redundant=srec.toRemove;
      ASS_NEQ(redundant, cl);

      BDDNode* oldRedundantProp=redundant->prop();

      if ( !bdd->isXOrNonYConstant(oldRedundantProp, cl->prop(), true) ) {
	//TODO: here the srec.replacement should probably be deleted
	continue;
      }

      Clause* replacement=srec.replacement;

      if (replacement) {
	addNewClause(replacement);
      }
      LOG_UNIT("sa_bw_simpl_red_clause",redundant);
      onClauseReduction(redundant, replacement, cl, 0, false);


      //we must remove the redundant clause before adding its replacement,
      //as otherwise the redundant one might demodulate the replacement into
      //a tautology

      redundant->incRefCnt(); //we don't want the clause deleted before we record the simplification

      removeActiveOrPassiveClause(redundant);

      redundant->setProp(bdd->getTrue());
      InferenceStore::instance()->recordPropReduce(redundant, oldRedundantProp, bdd->getTrue());


      TRACE("sa_bw_simpl",
	tout << "-<<--------\n";
	tout << ":" << (*cl) << endl;
	tout << "-" << (*redundant) << endl;
	if (replacement) {
	  tout << "+" << (*replacement) << endl;
	}
	tout << "removed\n";
	tout << "^^^^^^^^^^^\n";
      );

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
  CALL("SaturationAlgorithm::removeBackwardSimplifiedClause");

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
  case Clause::SELECTED_REACTIVATED:
    _active->remove(cl);
    break;
  case Clause::REACTIVATED:
    _passive->remove(cl);
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

  if (_bddMarkingSubsumption && _bddMarkingSubsumption->subsumed(cl)) {
    return false;
  }

  if (_consFinder && _consFinder->isRedundant(cl)) {
    return false;
  }

  if (_splitter && _opt.splitAtActivation()) {
    if (_splitter->doSplitting(cl)) {
      return false;
    }
  }

  _clauseActivationInProgress=true;

  if (!cl->selected()) {
    _selector->select(cl);
  }

  if (cl->store()==Clause::SELECTED_REACTIVATED) {
    cl->setStore(Clause::ACTIVE);
    env.statistics->reactivatedClauses++;
    LOG_UNIT("sa_reanimated", cl);
  } else {
    ASS_EQ(cl->store(), Clause::SELECTED);
    cl->setStore(Clause::ACTIVE);
    env.statistics->activeClauses++;

    _active->add(cl);
  }

  ClauseIterator toAdd=_generator->generateClauses(cl);

  while(toAdd.hasNext()) {
    Clause* genCl=toAdd.next();

    addNewClause(genCl);

    LOG_UNIT("sa_generated_clause", genCl);

    Inference::Iterator iit=genCl->inference()->iterator();
    while(genCl->inference()->hasNext(iit)) {
      Unit* premUnit=genCl->inference()->next(iit);
      ASS(premUnit->isClause());
      Clause* premCl=static_cast<Clause*>(premUnit);

      onParenthood(genCl, premCl);
    }
  }

  _clauseActivationInProgress=false;

  //now we remove clauses that could not be removed during the clause activation process
  while(_postponedClauseRemovals.isNonEmpty()) {
    Clause* cl=_postponedClauseRemovals.pop();
    if (cl->store()!=Clause::ACTIVE &&
	cl->store()!=Clause::PASSIVE &&
	cl->store()!=Clause::REACTIVATED &&
	cl->store()!=Clause::SELECTED_REACTIVATED) {
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

  if (cl->store()==Clause::SELECTED_REACTIVATED) {
    cl->setStore(Clause::ACTIVE);
  }
  else {
    ASS_EQ(cl->store(), Clause::SELECTED);
    cl->setStore(Clause::NONE);
  }
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
  while(qrit.hasNext()) {
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
    if (termReason == Statistics::SATISFIABLE && getOptions().proof()!=Options::PROOF_OFF) {
      res.saturatedSet = collectSaturatedSet();
    }
    throw MainLoopFinishedException(res);
  }

  Clause* cl = _passive->popSelected();

  if (cl->store()==Clause::REACTIVATED) {
    cl->setStore(Clause::SELECTED_REACTIVATED);
  }
  else {
    ASS_EQ(cl->store(),Clause::PASSIVE);
    cl->setStore(Clause::SELECTED);
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

  try
  {
    for (;;) {
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
 * of the forward simlifier and will take care of destroying it.
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
 * of the backward simlifier and will take care of destroying it.
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
  case Shell::Options::DISCOUNT:
    res=new Discount(prb, opt);
    break;
  case Shell::Options::LRS:
    res=new LRS(prb, opt);
    break;
  case Shell::Options::OTTER:
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
  if (opt.unitResultingResolution()!=Options::URR_OFF) {
    gie->addFront(new URResolution());
  }
  res->setGeneratingInferenceEngine(gie);

  res->setImmediateSimplificationEngine(createISE(prb, opt));

  // create forward simplification engine
  if (opt.hyperSuperposition()) {
    res->addForwardSimplifierToFront(new HyperSuperposition());
  }
  if (opt.globalSubsumption()) {
    res->addForwardSimplifierToFront(new GlobalSubsumption());
  }
  if (opt.forwardLiteralRewriting()) {
    res->addForwardSimplifierToFront(new ForwardLiteralRewriting());
  }
  if (prb.hasEquality()) {
    switch(opt.forwardDemodulation()) {
    case Options::DEMODULATION_ALL:
    case Options::DEMODULATION_PREORDERED:
      res->addForwardSimplifierToFront(new ForwardDemodulation());
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
      res->addForwardSimplifierToFront(new CTFwSubsAndRes(true));
    }
    else {
      res->addForwardSimplifierToFront(new CTFwSubsAndRes(false));
    }
  }
  else if (opt.forwardSubsumptionResolution()) {
    USER_ERROR("Forward subsumption resolution requires forward subsumption to be enabled.");
  }

  // create backward simplification engine
  if (prb.hasEquality()) {
    switch(opt.backwardDemodulation()) {
    case Options::DEMODULATION_ALL:
    case Options::DEMODULATION_PREORDERED:
      res->addBackwardSimplifierToFront(new BackwardDemodulation());
      break;
    case Options::DEMODULATION_OFF:
      break;
#if VDEBUG
    default:
      ASSERTION_VIOLATION;
#endif
    }
  }
  if (opt.backwardSubsumption()!=Options::SUBSUMPTION_OFF) {
    bool byUnitsOnly=opt.backwardSubsumption()==Options::SUBSUMPTION_UNIT_ONLY;
    res->addBackwardSimplifierToFront(new SLQueryBackwardSubsumption(byUnitsOnly));
  }
  if (opt.backwardSubsumptionResolution()!=Options::SUBSUMPTION_OFF) {
    bool byUnitsOnly=opt.backwardSubsumptionResolution()==Options::SUBSUMPTION_UNIT_ONLY;
    res->addBackwardSimplifierToFront(new BackwardSubsumptionResolution(byUnitsOnly));
  }

  if (opt.mode()==Options::MODE_CONSEQUENCE_ELIMINATION) {
    res->_consFinder=new ConsequenceFinder();
  }
  if (opt.showSymbolElimination()) {
    res->_symEl=new SymElOutput();
  }

  // switch(opt.splitting()) {
  // case Options::SM_OFF:
  //  break;
  // case Options::SM_BACKTRACKING:
  //   res->_splitter=new BSplitter();
  //   break;
  //case Options::SM_INPUT:
  //  res->_splitter=new SWBSplitterWithoutBDDs();
  //  break;
  //case Options::SM_SAT:
  // Splitting is now either on or off. If on it using SSplitter
  if(opt.splitting()){
    res->_splitter = new SSplitter();
  }
  if (opt.questionAnswering()==Options::QA_ANSWER_LITERAL) {
    res->_answerLiteralManager = AnswerLiteralManager::getInstance();
  }
  return res;
} // SaturationAlgorithm::createFromOptions

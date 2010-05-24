/**
 * @file SaturationAlgorithm.cpp
 * Implementing SaturationAlgorithm class.
 */

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
#include "Kernel/Inference.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/LiteralSelector.hpp"
#include "Kernel/MLVariant.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/SubformulaIterator.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "ConsequenceFinder.hpp"
#include "Splitter.hpp"
#include "SymElOutput.hpp"

#include "SaturationAlgorithm.hpp"



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


/**
 * A struct that is thrown as an exception when a refutation is found
 * during the saturation process.
 */
struct SaturationAlgorithm::RefutationFoundException
{
  RefutationFoundException(Clause* ref) : refutation(ref)
  {
    CALL("SaturationAlgorithm::RefutationFoundException::RefutationFoundException");
    ASS(isRefutation(ref));
  }

  Clause* refutation;
};


/**
 * Create a SaturationAlgorithm object
 *
 * The @b passiveContainer object will be used as a passive clause container, and
 * @b selector object to select literals before clauses are activated.
 */
SaturationAlgorithm::SaturationAlgorithm(PassiveClauseContainer* passiveContainer,
	LiteralSelector* selector)
: _imgr(this), _clauseActivationInProgress(false), _passive(passiveContainer),
  _fwSimplifiers(0), _bwSimplifiers(0), _selector(selector), _splitter(0),
  _consFinder(0), _symEl(0), _bddMarkingSubsumption(0)
{
  CALL("SaturationAlgorithm::SaturationAlgorithm");

  _propToBDD= env.options->propositionalToBDD();

  _unprocessed=new UnprocessedClauseContainer();
  _active=new ActiveClauseContainer();

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

  if(env.options->maxWeight()) {
    _limits.setLimits(0,env.options->maxWeight());
  }

  PassiveClauseContainer::registerInstance(_passive);
}

/**
 * Destroy the SaturationAlgorithm object
 */
SaturationAlgorithm::~SaturationAlgorithm()
{
  CALL("SaturationAlgorithm::~SaturationAlgorithm");

  env.statistics->finalActiveClauses=_active->size();
  env.statistics->finalPassiveClauses=_passive->size();

  PassiveClauseContainer::unregisterInstance(_passive);

  if(_splitter) {
    delete _splitter;
  }
  if(_consFinder) {
    delete _consFinder;
  }
  if(_symEl) {
    delete _symEl;
  }
  if(_bddMarkingSubsumption) {
    delete _bddMarkingSubsumption;
  }

  _active->detach();
  _passive->detach();

  if(_generator) {
    _generator->detach();
  }
  if(_immediateSimplifier) {
    _immediateSimplifier->detach();
  }

  while(_fwSimplifiers) {
    FwSimplList::pop(_fwSimplifiers)->detach();
  }
  while(_bwSimplifiers) {
    BwSimplList::pop(_bwSimplifiers)->detach();
  }

  delete _unprocessed;
  delete _active;
  delete _passive;

  delete _selector;
}

/**
 * Return true if the run of the prover so far is complete
 */
bool SaturationAlgorithm::isComplete()
{
  CALL("SaturationAlgorithm::isComplete");

  return env.options->complete();
}

ClauseIterator SaturationAlgorithm::activeClauses()
{
  CALL("SaturationAlgorithm::activeClauses");

  LiteralIndexingStructure* gis=getIndexManager()->getGeneratingLiteralIndexingStructure();

  return pvi( getMappingIterator(gis->getAll(), SLQueryResult::ClauseExtractFn()) );
}

ClauseIterator SaturationAlgorithm::passiveClauses()
{
  CALL("SaturationAlgorithm::passiveClauses");

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
#if REPORT_CONTAINERS
  cout<<"## Active added: "<<(*c)<<endl;
#endif

  if(env.options->showActive()) {
    cout<<"Active: "<<c->toNiceString()<<endl;
  }
}

/**
 * A function that is called when a clause is removed from the active clause container.
 */
void SaturationAlgorithm::onActiveRemoved(Clause* c)
{
  CALL("SaturationAlgorithm::onActiveRemoved");

#if REPORT_CONTAINERS
  cout<<"== Active removed: "<<(*c)<<endl;
#endif

  ASS(c->store()==Clause::ACTIVE || c->store()==Clause::REACTIVATED ||
      c->store()==Clause::SELECTED_REACTIVATED);

  if(c->store()==Clause::ACTIVE) {
    c->setStore(Clause::NONE);
    //at this point the c object may be deleted
  } else if(c->store()==Clause::REACTIVATED) {
    c->setStore(Clause::PASSIVE);
  } else if(c->store()==Clause::SELECTED_REACTIVATED) {
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
  CALL("SaturationAlgorithm::beforeClauseActivation");
  ASS(clausesFlushed());

  if(_symEl) {
    _symEl->onAllProcessed();
  }

  if(_splitter) {
    _splitter->onAllProcessed();
  }

  if(_bddMarkingSubsumption) {
    _bddMarkingSubsumption->onAllProcessed();
  }
}

/**
 * A function that is called when a clause is added to the passive clause container.
 */
void SaturationAlgorithm::onPassiveAdded(Clause* c)
{
#if REPORT_CONTAINERS
  cout<<"# Passive added: "<<(*c)<<endl;
#endif

  //when a clause is added to the passive container,
  //we know it is not redundant
  onNonRedundantClause(c);

  if(env.options->showPassive()) {
    cout<<"Passive: "<<c->toNiceString()<<endl;
  }
}

/**
 * A function that is called when a clause is removed from the active clause container.
 * The function is not called when a selected clause is removed from the passive container.
 * In this case the @b onPassiveSelected method is called.
 */
void SaturationAlgorithm::onPassiveRemoved(Clause* c)
{
  CALL("SaturationAlgorithm::onPassiveRemoved");

#if REPORT_CONTAINERS
  cout<<"= Passive removed: "<<(*c)<<endl;
#endif

  ASS(c->store()==Clause::PASSIVE || c->store()==Clause::REACTIVATED)

  if(c->store()==Clause::PASSIVE) {
    c->setStore(Clause::NONE);
    //at this point the c object can be deleted
  } else if(c->store()==Clause::REACTIVATED) {
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
#if REPORT_CONTAINERS
  cout<<"~ Passive selected: "<<(*c)<<endl;
#endif
}

/**
 * A function that is called when a clause is added to the unprocessed clause container.
 */
void SaturationAlgorithm::onUnprocessedAdded(Clause* c)
{
#if REPORT_CONTAINERS
  cout<<"++ Unprocessed added: "<<(*c)<<endl;
#endif
}

/**
 * A function that is called when a clause is removed from the active clause container.
 */
void SaturationAlgorithm::onUnprocessedRemoved(Clause* c)
{
#if REPORT_CONTAINERS
  cout<<"-- Unprocessed removed: "<<(*c)<<endl;
#endif
}

void SaturationAlgorithm::onUnprocessedSelected(Clause* c)
{
#if REPORT_CONTAINERS
  cout<<"~~ Unprocessed selected: "<<(*c)<<endl;
#endif
}

/**
 * A function that is called whenever a possibly new clause appears.
 */
void SaturationAlgorithm::onNewClause(Clause* cl)
{
  CALL("SaturationAlgorithm::onNewClause");

  if(_splitter) {
    _splitter->onNewClause(cl);
  }

  if(!cl->prop()) {
    BDD* bdd=BDD::instance();
    BDDNode* prop=bdd->getFalse();

    Inference* inf=cl->inference();
    Inference::Iterator it=inf->iterator();
    while(inf->hasNext(it)) {
      Unit* premu=inf->next(it);
      if(!premu->isClause()) {
	//the premise comes from preprocessing
	continue;
      }
      Clause* prem=static_cast<Clause*>(premu);
      if(!prem->prop()) {
	//the premise comes from preprocessing
	continue;
      }

      prop=bdd->disjunction(prop, prem->prop());
    }

    cl->initProp(prop);
    if(!bdd->isTrue(prop)) {
      InferenceStore::instance()->recordNonPropInference(cl);
    }
  }

  if(env.options->showNew()) {
    cout<<"New: "<<cl->toNiceString()<<endl;
//    cout<<"New: "<<cl->toString()<<endl;
  }

  if(!_propToBDD && cl->isPropositional()) {
    onNewUsefulPropositionalClause(cl);
  }
}

void SaturationAlgorithm::onNewUsefulPropositionalClause(Clause* c)
{
  CALL("SaturationAlgorithm::onNewUsefulPropositionalClause");
  ASS(c->isPropositional());

  if(env.options->showNewPropositional()) {
    VirtualIterator<string> clStrings=c->toSimpleClauseStrings();
    while(clStrings.hasNext()) {
      cout<<"New propositional: "<<clStrings.next()<<endl;
    }
  }

  if(_bddMarkingSubsumption) {
    _bddMarkingSubsumption->onNewPropositionalClause(c);
  }

  if(_consFinder) {
    _consFinder->onNewPropositionalClause(c);
  }
}

/**
 * Called when a clause successfully passes the forward simplification
 */
void SaturationAlgorithm::onClauseRetained(Clause* cl)
{
  CALL("SaturationAlgorithm::onClauseRetained");
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
  
  if(reductionPremise) {
    ASS(premise);
    premises = pvi( getConcatenatedIterator(getSingletonIterator(premise), getSingletonIterator(reductionPremise)) );
  }
  else if(premise) {
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

  if(replacement && BDD::instance()->isTrue(replacement->prop())) {
    //clause was rewritten into tautology, so we look at it as if
    //it was just deleted
    replacement=0;
  }

  static ClauseStack premStack;
  premStack.reset();
  premStack.loadFromIterator(premises);

  if(_splitter) {
    _splitter->onClauseReduction(cl, pvi( ClauseStack::Iterator(premStack) ), replacement);
  }

  if(replacement) {
    onParenthood(replacement, cl);
    while(premStack.isNonEmpty()) {
      onParenthood(replacement, premStack.pop());
    }
  }
}


void SaturationAlgorithm::onNonRedundantClause(Clause* c)
{
  CALL("SaturationAlgorithm::onNonRedundantClause");

  if(_symEl) {
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

  if(_symEl) {
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

  if(_symEl) {
    _symEl->onInputClause(cl);
  }

  if(_propToBDD) {
    //put propositional predicates into BDD part
    cl=_propToBDDConv.simplify(cl);
    if(!cl) {
      return;
    }
  }

  if(env.options->sos() && cl->inputType()==Clause::AXIOM) {
    addInputSOSClause(cl);
  } else {
    addNewClause(cl);
  }

  env.statistics->initialClauses++;
}

/**
 * Add an input set-of-support clause @b cl into the active container
 */
void SaturationAlgorithm::addInputSOSClause(Clause* cl)
{
  CALL("SaturationAlgorithm::addInputSOSClause");
  ASS_EQ(cl->inputType(),Clause::AXIOM);

  onNewClause(cl);

simpl_start:

  Clause* simplCl=_immediateSimplifier->simplify(cl);
  if(simplCl!=cl) {
    if(!simplCl) {
      onClauseReduction(cl, 0, 0);
      return;
    }
    onNewClause(simplCl);
    onClauseReduction(cl, simplCl, 0);
    cl=simplCl;
    goto simpl_start;
  }

  if(cl->isEmpty()) {
    addNewClause(cl);
    return;
  }

  ASS(!cl->selected());
  _selector->select(cl);

  cl->setStore(Clause::ACTIVE);
  env.statistics->activeClauses++;
  _active->add(cl);

  onSOSClauseAdded(cl);
}


/**
 * Insert input clauses into the SaturationAlgorithm object.
 *
 * It usually means adding all clauses yielded by the @b toAdd iterator
 * into the unprocessed container, but not always (see the set-of-support
 * option).
 */
void SaturationAlgorithm::addInputClauses(ClauseIterator toAdd)
{
  CALL("SaturationAlgorithm::addInputClauses");

  while(toAdd.hasNext()) {
    Clause* cl=toAdd.next();
    addInputClause(cl);
  }
}

/**
 * Return true iff clause @b c is refutation clause.
 *
 * Deriving a refutation clause means that the saturation algorithm can
 * terminate with success.
 */
bool SaturationAlgorithm::isRefutation(Clause* c)
{
  CALL("SaturationAlgorithm::isRefutation");
  ASS(c->prop());

  BDD* bdd=BDD::instance();
  return c->isEmpty() && bdd->isFalse(c->prop()) && c->noSplits();
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

#if REPORT_FW_SIMPL
    cout<<"->>--------\n";
    ClauseList* lst=0;
    while(premises.hasNext()) {
      Clause* premise=premises.next();
      ASS(willPerform(premise));
      ClauseList::push(premise, lst);
      cout<<":"<<(*premise)<<endl;
    }
    cout<<"-"<<(*_cl)<<endl;
    premises=pvi( ClauseList::DestructiveIterator(lst) );
#endif

    if(replacement) {
      replacement->initProp(oldClProp);
      InferenceStore::instance()->recordNonPropInference(replacement);
      _sa->addNewClause(replacement);
    }
    _sa->onClauseReduction(_cl, replacement, premises);

    _cl->setProp(bdd->getTrue());
    InferenceStore::instance()->recordPropReduce(_cl, oldClProp, bdd->getTrue());
    _cl=0;

#if REPORT_FW_SIMPL
    if(replacement) {
      cout<<"+"<<(*replacement)<<endl;
    }
    cout<<"removed\n";
    cout<<"^^^^^^^^^^^^\n";
#endif
  }

  bool willPerform(Clause* premise)
  {
    CALL("TotalSimplificationPerformer::willPerform");
    ASS(_cl);

    if(!premise) {
      return true;
    }

    if( (_cl->color()|premise->color())==COLOR_INVALID ) {
      return false;
    }

    BDD* bdd=BDD::instance();
    if(!bdd->isXOrNonYConstant(_cl->prop(), premise->prop(), true)) {
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
  if(simplCl!=cl) {
    if(simplCl) {
      addNewClause(simplCl);
    }
    onClauseReduction(cl, simplCl, 0);
    return 0;
  }

  if(cl!=cl0 && cl0->isInput()) {
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

  onNewClause(cl);

  ASS(cl->prop());
  if(BDD::instance()->isTrue(cl->prop())) {
    return;
  }

  if(_bddMarkingSubsumption && _bddMarkingSubsumption->subsumed(cl)) {
    return;
  }

  _newClauses.push(cl);
}

void SaturationAlgorithm::newClausesToUnprocessed()
{
  CALL("SaturationAlgorithm::newClausesToUnprocessed");

  while(_newClauses.isNonEmpty()) {
    Clause* cl=_newClauses.popWithoutDec();

    if(BDD::instance()->isTrue(cl->prop())) {
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

#if REPORT_CONTAINERS
  cout<<"$$ Unprocessed adding: "<<(*cl)<<endl;
#endif


  env.statistics->generatedClauses++;

  BDD* bdd=BDD::instance();
  ASS(!bdd->isTrue(cl->prop()));

  env.checkTimeSometime<64>();

  cl=doImmediateSimplification(cl);
  if(!cl) {
    return;
  }
  ASS(!bdd->isTrue(cl->prop()));

  if(cl->isEmpty()) {
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

  if(isRefutation(cl)) {
    onNonRedundantClause(cl);
    throw RefutationFoundException(cl);
  }

  if(_splitter && _splitter->handleEmptyClause(cl)) {
    return;
  }

  BDD* bdd=BDD::instance();

  ASS(!bdd->isFalse(cl->prop()));
  env.statistics->bddPropClauses++;

  if(env.options->satSolverForEmptyClause()) {
    static BDDConjunction ecProp;
    static Stack<InferenceStore::ClauseSpec> emptyClauses;

    onNonRedundantClause(cl);
    onNewUsefulPropositionalClause(cl);
    ecProp.addNode(cl->prop());
    if(ecProp.isFalse()) {
      InferenceStore::instance()->recordMerge(cl, cl->prop(), emptyClauses.begin(),
	      emptyClauses.size(), bdd->getFalse());
      cl->setProp(bdd->getFalse());
      onNewUsefulPropositionalClause(cl);
      onNonRedundantClause(cl);
      throw RefutationFoundException(cl);
    } else {
      cl->incRefCnt();
      emptyClauses.push(InferenceStore::getClauseSpec(cl));
      return;
    }
  } else {
    static Clause* accumulator=0;
    if(accumulator==0) {
      cl->incRefCnt();
      onNonRedundantClause(cl);
      accumulator=cl;
      onNewUsefulPropositionalClause(cl);
      return;
    }
    BDDNode* newProp=bdd->conjunction(accumulator->prop(), cl->prop());
    if(newProp!=accumulator->prop()) {
      onNonRedundantClause(cl);
      onNewUsefulPropositionalClause(cl);
    }
    if(bdd->isFalse(newProp)) {
      InferenceStore::instance()->recordMerge(cl, cl->prop(), accumulator, newProp);
      cl->setProp(newProp);
      onNonRedundantClause(cl);
      onNewUsefulPropositionalClause(cl);
      throw RefutationFoundException(cl);
    }
    if(newProp!=accumulator->prop()) {
      InferenceStore::instance()->recordMerge(accumulator, accumulator->prop(), cl, newProp);
      accumulator->setProp(newProp);
      onNonRedundantClause(accumulator);
    } else {
      env.statistics->subsumedEmptyClauses++;
      if(env.options->emptyClauseSubsumption()) {
	performEmptyClauseParentSubsumption(cl, accumulator->prop());
      }
    }
  }
}

/**
 * Perform a kind of backward subsumption by an empty clause, assuming that
 * the propositional part of the empty clause is @b emptyClauseProp.
 *
 * The subsumption checks only clauses that are ancestors of @b cl. First
 * its parents is checked for being subsumed, and if some is, its parents
 * are checked as well etc...
 *
 * The deletion of subsumed clauses is performed by the @b removeBackwardSimplifiedClause
 * function. As the @b performEmptyClauseSubsumption is to be called during
 * clause activation, when some indexes are being traversed (and so cannot
 * be modified), the clause deletion is postponed by the @b removeBackwardSimplifiedClause
 * until the clause activation is over.
 */
void SaturationAlgorithm::performEmptyClauseParentSubsumption(Clause* cl0, BDDNode* emptyClauseProp)
{
  CALL("SaturationAlgorithm::performEmptyClauseSubsumption");
  ASS(cl0->isEmpty());

  BDD* bdd=BDD::instance();

  static Stack<Clause*> parentsToCheck;
  ASS(parentsToCheck.isEmpty());

  Clause* cl=cl0;
  for(;;) {
    VirtualIterator<InferenceStore::ClauseSpec> parents=InferenceStore::instance()->getParents(cl);

    while(parents.hasNext()) {
      Clause* par=parents.next().first;
      if(par->store()!=Clause::ACTIVE &&
	  par->store()!=Clause::PASSIVE &&
	  par->store()!=Clause::REACTIVATED) {
	continue;
      }
      if(!par->prop() || bdd->isTrue(par->prop())) {
	continue;
      }
      if(!bdd->isXOrNonYConstant(par->prop(), emptyClauseProp, true)) {
	continue;
      }
      par->setProp(bdd->getTrue());
      removeActiveOrPassiveClause(par);
      env.statistics->emptyClauseSubsumptions++;
      //Here we assume that the clause object did not get deleted!
      //(it is fine at the time of writing this function,
      //as we now do not delete any clause objects)
      parentsToCheck.push(par);
    }

    if(parentsToCheck.isEmpty()) {
      break;
    }
    cl=parentsToCheck.pop();
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

  if(cl->store()==Clause::REACTIVATED || cl->store()==Clause::SELECTED_REACTIVATED) {
    return true;
  }

  if(!getLimits()->fulfillsLimits(cl)) {
    env.statistics->discardedNonRedundantClauses++;
    return false;
  }

  TotalSimplificationPerformer performer(this, cl);

  FwSimplList::Iterator fsit(_fwSimplifiers);

  while(fsit.hasNext()) {
    ForwardSimplificationEngine* fse=fsit.next().ptr();

    fse->perform(cl, &performer);
    if(!performer.clauseKept()) {
      break;
    }
  }

  //TODO: hack that only clauses deleted by forward simplification can be destroyed (other destruction needs debugging)
  if(performer.clauseKept()) {
    cl->incRefCnt();
  }

  if(!performer.clauseKept()) {
    return false;
  }


  if( _splitter && !env.options->splitAtActivation() ) {
    if(_splitter->doSplitting(cl)) {
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
    BackwardSimplificationEngine* bse=bsit.next().ptr();

    BwSimplificationRecordIterator simplifications;
    bse->perform(cl,simplifications);
    while(simplifications.hasNext()) {
      BwSimplificationRecord srec=simplifications.next();
      Clause* redundant=srec.toRemove;
      ASS_NEQ(redundant, cl);

      BDDNode* oldRedundantProp=redundant->prop();

      if( !bdd->isXOrNonYConstant(oldRedundantProp, cl->prop(), true) ) {
	continue;
      }


#if REPORT_BW_SIMPL
      cout<<"-<<--------\n";
      cout<<":"<<(*cl)<<endl;
      cout<<"-"<<(*redundant)<<endl;
#endif

      Clause* replacement=srec.replacement;

      if(replacement) {
	addNewClause(replacement);

#if REPORT_BW_SIMPL
	cout<<"+"<<(*replacement)<<endl;
#endif
      }
      onClauseReduction(redundant, replacement, cl, 0, false);


      //we must remove the redundant clause before adding its replacement,
      //as otherwise the redundant one might demodulate the replacement into
      //a tautology

      redundant->incRefCnt(); //we don't want the clause deleted before we record the simplification

      removeActiveOrPassiveClause(redundant);

      redundant->setProp(bdd->getTrue());
      InferenceStore::instance()->recordPropReduce(redundant, oldRedundantProp, bdd->getTrue());

      redundant->decRefCnt();

#if REPORT_BW_SIMPL
      cout<<"removed\n";
      cout<<"^^^^^^^^^^^\n";
#endif
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

  if(_clauseActivationInProgress) {
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
    ASS_REP(false, cl->store());
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

  if(_bddMarkingSubsumption && _bddMarkingSubsumption->subsumed(cl)) {
    return false;
  }

  if(_consFinder && _consFinder->isRedundant(cl)) {
    return false;
  }

  if(_splitter && env.options->splitAtActivation()) {
    if(_splitter->doSplitting(cl)) {
      return false;
    }
  }

  _clauseActivationInProgress=true;

  if(!cl->selected()) {
    _selector->select(cl);
  }

  if(cl->store()==Clause::SELECTED_REACTIVATED) {
    cl->setStore(Clause::ACTIVE);
    env.statistics->reactivatedClauses++;
#if REPORT_CONTAINERS
    cout<<"** Reanimated: "<<(*cl)<<endl;
#endif
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

#if REPORT_CONTAINERS
    cout<<"G "<<(*genCl)<<endl;
#endif

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
    if(cl->store()!=Clause::ACTIVE &&
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

    if(forwardSimplify(c)) {
      onClauseRetained(c);
      addToPassive(c);
      ASS_EQ(c->store(), Clause::PASSIVE);
    }
    else {
      ASS_EQ(c->store(), Clause::UNPROCESSED);
      c->setStore(Clause::NONE);
    }

    newClausesToUnprocessed();

    if(env.timeLimitReached()) {
      throw TimeLimitExceededException();
    }
  }

  ASS(clausesFlushed());
  onAllProcessed();
  if(!clausesFlushed()) {
    //there were some new clauses added, so let's process them
    goto start;
  }

}

void SaturationAlgorithm::handleUnsuccessfulActivation(Clause* cl)
{
  CALL("SaturationAlgorithm::handleUnsuccessfulActivation");

  if(cl->store()==Clause::SELECTED_REACTIVATED) {
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
 * Perform saturation on clauses that were added through
 * @b addInputClauses function
 */
SaturationResult SaturationAlgorithm::saturate()
{
  CALL("SaturationAlgorithm::saturate");

  _sharing.init(this);
  if(_splitter) {
    _splitter->init(this);
  }
  if(_consFinder) {
    _consFinder->init(this);
  }
  if(_symEl) {
    _symEl->init(this);
  }
  if(_bddMarkingSubsumption) {
    _bddMarkingSubsumption->init(this);
  }

  _startTime=env.timer->elapsedMilliseconds();

  try
  {
    for (;;) {
      doUnprocessedLoop();

      if(_passive->isEmpty()) {
        return SaturationResult(isComplete() ? Statistics::SATISFIABLE : Statistics::REFUTATION_NOT_FOUND);
      }

      Clause* cl = _passive->popSelected();

      if(cl->store()==Clause::REACTIVATED) {
	cl->setStore(Clause::SELECTED_REACTIVATED);
      }
      else {
	ASS_EQ(cl->store(),Clause::PASSIVE);
	cl->setStore(Clause::SELECTED);
      }

      if(!handleClauseBeforeActivation(cl)) {
        continue;
      }

      bool isActivated=activate(cl);
      if(!isActivated) {
        handleUnsuccessfulActivation(cl);
      }

      if(env.timeLimitReached()) {
        return SaturationResult(Statistics::TIME_LIMIT);
      }
    }
  }
  catch(RefutationFoundException rs)
  {
    return SaturationResult(Statistics::REFUTATION, rs.refutation);
  }
  catch(TimeLimitExceededException)
  {
    return SaturationResult(Statistics::TIME_LIMIT);
  }
}

/**
 * Assign an generating inference object @b generator to be used
 *
 * To use multiple generating inferences, use the @b CompositeGIE
 * object.
 */
void SaturationAlgorithm::setGeneratingInferenceEngine(GeneratingInferenceEngineSP generator)
{
  ASS(!_generator);
  _generator=generator;
  _generator->attach(this);
}

/**
 * Assign an immediate simplifier object @b immediateSimplifier
 * to be used
 *
 * For description of what an immediate simplifier is, see
 * @b ImmediateSimplificationEngine documentation.
 *
 * To use multiple immediate simplifiers, use the @b CompositeISE
 * object.
 */
void SaturationAlgorithm::setImmediateSimplificationEngine(ImmediateSimplificationEngineSP immediateSimplifier)
{
  ASS(!_immediateSimplifier);
  _immediateSimplifier=immediateSimplifier;
  _immediateSimplifier->attach(this);
}

/**
 * Add a forward simplifier, so that it is applied before the
 * simplifiers that were added before it.
 *
 * Forward demodulation simplifier should be added by the
 * @b setFwDemodulator function, not by this one.
 */
void SaturationAlgorithm::addForwardSimplifierToFront(ForwardSimplificationEngineSP fwSimplifier)
{
  FwSimplList::push(fwSimplifier, _fwSimplifiers);
  fwSimplifier->attach(this);
}

/**
 * Add a backward simplifier, so that it is applied before the
 * simplifiers that were added before it.
 */
void SaturationAlgorithm::addBackwardSimplifierToFront(BackwardSimplificationEngineSP bwSimplifier)
{
  BwSimplList::push(bwSimplifier, _bwSimplifiers);
  bwSimplifier->attach(this);
}

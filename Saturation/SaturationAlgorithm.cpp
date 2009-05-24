/**
 * @file SaturationAlgorithm.cpp
 * Implementing SaturationAlgorithm class.
 */

#include "../Lib/Environment.hpp"
#include "../Lib/VirtualIterator.hpp"
#include "../Kernel/BDD.hpp"
#include "../Kernel/Clause.hpp"
#include "../Kernel/Inference.hpp"
#include "../Kernel/LiteralSelector.hpp"
#include "../Shell/Statistics.hpp"

#include "SaturationAlgorithm.hpp"


#include "../Kernel/MLVariant.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Shell;
using namespace Saturation;

#define REPORT_CONTAINERS 0
#define REPORT_FW_SIMPL 0
#define REPORT_BW_SIMPL 0

SaturationAlgorithm::SaturationAlgorithm(PassiveClauseContainerSP passiveContainer,
	LiteralSelectorSP selector)
: _imgr(this), _passive(passiveContainer), _fwSimplifiers(0), _bwSimplifiers(0), _selector(selector)
{
  _unprocessed=new UnprocessedClauseContainer();
  _active=new ActiveClauseContainer();

  _active->attach(this);
  _passive->attach(this);

//  _active->addedEvent.subscribe(this,&SaturationAlgorithm::onActiveAdded);
//  _active->removedEvent.subscribe(this,&SaturationAlgorithm::onActiveRemoved);

#if REPORT_CONTAINERS
  _active->addedEvent.subscribe(this,&SaturationAlgorithm::onActiveAdded);
  _active->removedEvent.subscribe(this,&SaturationAlgorithm::onActiveRemoved);
  _passive->addedEvent.subscribe(this,&SaturationAlgorithm::onPassiveAdded);
  _passive->removedEvent.subscribe(this,&SaturationAlgorithm::onPassiveRemoved);
  _passive->selectedEvent.subscribe(this,&SaturationAlgorithm::onPassiveSelected);
  _unprocessed->addedEvent.subscribe(this,&SaturationAlgorithm::onUnprocessedAdded);
  _unprocessed->removedEvent.subscribe(this,&SaturationAlgorithm::onUnprocessedRemoved);
  _unprocessed->selectedEvent.subscribe(this,&SaturationAlgorithm::onUnprocessedSelected);
#endif

}

SaturationAlgorithm::~SaturationAlgorithm()
{
  env.statistics->finalActiveClauses=_active->size();
  env.statistics->finalPassiveClauses=_passive->size();

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
}

void SaturationAlgorithm::onActiveAdded(Clause* c)
{
  cout<<"## Active added: "<<(*c)<<endl;
}
void SaturationAlgorithm::onActiveRemoved(Clause* c)
{
  cout<<"== Active removed: "<<(*c)<<endl;
}
void SaturationAlgorithm::onPassiveAdded(Clause* c)
{
  cout<<"# Passive added: "<<(*c)<<endl;
}
void SaturationAlgorithm::onPassiveRemoved(Clause* c)
{
  cout<<"= Passive removed: "<<(*c)<<endl;
}
void SaturationAlgorithm::onPassiveSelected(Clause* c)
{
  cout<<"~ Passive selected: "<<(*c)<<endl;
}
void SaturationAlgorithm::onUnprocessedAdded(Clause* c)
{
  cout<<"++ Unprocessed added: "<<(*c)<<endl;
}
void SaturationAlgorithm::onUnprocessedRemoved(Clause* c)
{
  cout<<"-- Unprocessed removed: "<<(*c)<<endl;
}
void SaturationAlgorithm::onUnprocessedSelected(Clause* c)
{
  cout<<"~~ Unprocessed selected: "<<(*c)<<endl;
}


/**
 * Insert input clauses into ste unprocessed container.
 */
void SaturationAlgorithm::addInputClauses(ClauseIterator toAdd)
{
  BDD* bdd=BDD::instance();
  while(toAdd.hasNext()) {
    Clause* cl=toAdd.next();
    ASS_EQ(cl->prop(),0);
    cl->setProp(bdd->getFalse());
    addUnprocessedClause(cl);
  }
}

bool SaturationAlgorithm::isRefutation(Clause* c)
{
  CALL("SaturationAlgorithm::isRefutation");
  ASS(c->prop());

  BDD* bdd=BDD::instance();
  return c->isEmpty() && bdd->isFalse(c->prop());
}

/**
 * Perform immediate simplifications on a clause and add it
 * to unprocessed.
 *
 * Splitting is also being performed in this method.
 */
void SaturationAlgorithm::addUnprocessedClause(Clause* cl)
{
  CALL("SaturationAlgorithm::addUnprocessedClause");
  ASS(cl->prop());

  env.statistics->generatedClauses++;

  BDD* bdd=BDD::instance();
  ASS(!bdd->isTrue(cl->prop()));

  BDDNode* prop=cl->prop();
  bool simplified;
  do {
    Clause* simplCl=_immediateSimplifier->simplify(cl);
    if(simplCl==0) {
      return;
    }
    simplified=simplCl!=cl;
    if(simplified) {
      cl=simplCl;
      cl->setProp(prop);
    }
  } while(simplified);

  ASS(!bdd->isTrue(cl->prop()));
/**/
  ClauseIterator newComponents;
  ClauseIterator modifiedComponents;
  _splitter.doSplitting(cl, newComponents, modifiedComponents);
  while(newComponents.hasNext()) {
    Clause* comp=newComponents.next();
    ASS_EQ(comp->store(), Clause::NONE);
    ASS(!bdd->isTrue(comp->prop()));

    if(!bdd->isTrue(comp->prop())) {
      comp->setStore(Clause::UNPROCESSED);
      _unprocessed->add(comp);
    }
  }
  while(modifiedComponents.hasNext()) {
    Clause* comp=modifiedComponents.next();

    ASS(!bdd->isTrue(comp->prop()));
    if(comp->store()==Clause::ACTIVE) {
      if(!comp->isEmpty()) { //don't reanimate empty clause
	reanimate(comp);
      } else {
	ASS(!isRefutation(comp));
      }
    } else if(comp->store()==Clause::NONE) {
      ASS(!comp->isEmpty());
      comp->setStore(Clause::UNPROCESSED);
      _unprocessed->add(comp);
    }
  }
/*/
  cl->setStore(Clause::UNPROCESSED);
  _unprocessed->add(cl);
/**/
}

void SaturationAlgorithm::reanimate(Clause* cl)
{
  CALL("SaturationAlgorithm::reanimate");
  ASS_EQ(cl->store(), Clause::ACTIVE);

  ASS(!BDD::instance()->isTrue(cl->prop()));

  cl->setStore(Clause::REACTIVATED);
  _passive->add(cl);
}

class ForwardSimplificationPerformerImpl
: public ForwardSimplificationPerformer
{
public:
  ForwardSimplificationPerformerImpl(Clause* cl) : _cl(cl), _toAddLst(0) {}

  ~ForwardSimplificationPerformerImpl() { _toAddLst->destroy(); }

  void perform(Clause* premise, Clause* replacement)
  {
    CALL("ForwardSimplificationPerformerImpl::perform");
    ASS(_cl);

    BDD* bdd=BDD::instance();

    BDDNode* oldClProp=_cl->prop();

#if REPORT_FW_SIMPL
    cout<<"->>--------\n";
#endif

    BDDNode* premiseProp = premise ? premise->prop() : bdd->getFalse();
#if REPORT_FW_SIMPL
    if(premise) {
      cout<<":"<<(*premise)<<endl;
    }
#endif

    if(replacement) {
      BDDNode* replacementProp=bdd->disjunction(oldClProp, premiseProp);
      if(!bdd->isTrue(replacementProp)) {
	replacement->setProp(replacementProp);
#if REPORT_FW_SIMPL
	cout<<"#"<<(*replacement)<<endl;
#endif
	ClauseList::push(replacement, _toAddLst);
      }
    }

#if REPORT_FW_SIMPL
    cout<<"="<<(*_cl)<<endl;
#endif
    _cl->setProp(bdd->xOrNonY(oldClProp, premiseProp));

    if(bdd->isTrue(_cl->prop())) {
      _cl=0;
#if REPORT_FW_SIMPL
      cout<<"removed\n";
      cout<<"^^^^^^^^^^^^\n";
#endif
    }
#if REPORT_FW_SIMPL
    if(_cl) {
      cout<<">"<<(*_cl)<<endl;
      cout<<"^^^^^^^^^^^\n";
    }
#endif
  }

  bool clauseKept()
  { return _cl; }

  ClauseIterator clausesToAdd()
  { return pvi( ClauseList::Iterator(_toAddLst) ); }
private:
  Clause* _cl;
  ClauseList* _toAddLst;
};

bool SaturationAlgorithm::forwardSimplify(Clause* cl)
{
  CALL("SaturationAlgorithm::forwardSimplify");

  if(cl->store()==Clause::REACTIVATED) {
    return true;
  }

  BDD* bdd=BDD::instance();

  if(!getLimits()->fulfillsLimits(cl)) {
    return false;
  }

  ForwardSimplificationPerformerImpl performer(cl);

  FwSimplList::Iterator fsit(_fwSimplifiers);
  while(fsit.hasNext()) {
    ForwardSimplificationEngine* fse=fsit.next().ptr();

    fse->perform(cl, &performer);
    if(!performer.clauseKept()) {
      break;
    }
  }
  ClauseIterator replacements=performer.clausesToAdd();
  while(replacements.hasNext()) {
    addUnprocessedClause(replacements.next());
  }

  return performer.clauseKept();
}

void SaturationAlgorithm::backwardSimplify(Clause* cl)
{
  CALL("SaturationAlgorithm::backwardSimplify");

  if(cl->store()==Clause::REACTIVATED) {
    return;
  }

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

#if REPORT_BW_SIMPL
      cout<<"-<<--------\n";
      cout<<":"<<(*cl)<<endl;
      cout<<"="<<(*redundant)<<endl;

      if(MLVariant::isVariant(cl, redundant)) {
	cout<<"Variant!!!\n";
      }
#endif

      BDDNode* oldRedundantProp=redundant->prop();
      BDDNode* newRedundantProp=bdd->xOrNonY(oldRedundantProp, cl->prop());

//      if( newRedundantProp==oldRedundantProp && !bdd->isTrue(oldRedundantProp) ) {
      if( newRedundantProp==oldRedundantProp ) {
	continue;
      }

      if(srec.replacements.hasNext()) {
	BDDNode* replacementProp=bdd->disjunction(oldRedundantProp, cl->prop());
	if(!bdd->isTrue(replacementProp)) {
	  while(srec.replacements.hasNext()) {
	    Clause* addCl=srec.replacements.next();
	    addCl->setProp(replacementProp);
	    addUnprocessedClause(addCl);
	  }
	}
      }

      redundant->setProp(newRedundantProp);

      if(bdd->isTrue(newRedundantProp)) {
	switch(redundant->store()) {
	case Clause::PASSIVE:
	  _passive->remove(redundant);
	  break;
	case Clause::ACTIVE:
	  _active->remove(redundant);
	  break;
	case Clause::REACTIVATED:
	  _passive->remove(redundant);
	  _active->remove(redundant);
	  break;
	default:
	  ASSERTION_VIOLATION;
	}
	redundant->setStore(Clause::NONE);
#if REPORT_BW_SIMPL
	cout<<"removed\n";
#endif
      } else if(redundant->store()==Clause::ACTIVE) {
	reanimate(redundant);
      }
#if REPORT_BW_SIMPL
      cout<<"^^^^^^^^^^^\n";
#endif
    }
  }
}

void SaturationAlgorithm::addToPassive(Clause* c)
{
  CALL("SaturationAlgorithm::addToPassive");

  ASS_EQ(c->store(), Clause::UNPROCESSED);
  c->setStore(Clause::PASSIVE);
  env.statistics->passiveClauses++;

  _passive->add(c);
}

void SaturationAlgorithm::activate(Clause* cl)
{
  CALL("SaturationAlgorithm::activate");

  if(!cl->selected()) {
    _selector->select(cl);
  }

  if(cl->store()==Clause::REACTIVATED) {
    cl->setStore(Clause::ACTIVE);
#if REPORT_CONTAINERS
    cout<<"** Reanimated: "<<(*cl)<<endl;
#endif
  } else {
    ASS_EQ(cl->store(), Clause::PASSIVE);
    cl->setStore(Clause::ACTIVE);
    env.statistics->activeClauses++;

    _active->add(cl);
  }

  ClauseIterator toAdd=_generator->generateClauses(cl);

  BDD* bdd=BDD::instance();
  while(toAdd.hasNext()) {
    Clause* genCl=toAdd.next();

    BDDNode* prop=bdd->getFalse();
    Inference::Iterator iit=genCl->inference()->iterator();
    while(genCl->inference()->hasNext(iit)) {
      Unit* premUnit=genCl->inference()->next(iit);
      ASS(premUnit->isClause());
      Clause* premCl=static_cast<Clause*>(premUnit);
//      cout<<"premCl: "<<(*premCl)<<endl;
      prop=bdd->disjunction(prop, premCl->prop());
//      cout<<"res: "<<bdd->toString(prop)<<endl;
    }


    genCl->setProp(prop);
#if REPORT_CONTAINERS
    cout<<"G "<<(*genCl)<<endl;
#endif

    if(bdd->isTrue(prop)) {
      continue;
    }

    addUnprocessedClause(genCl);
  }
}

void SaturationAlgorithm::setGeneratingInferenceEngine(GeneratingInferenceEngineSP generator)
{
  ASS(!_generator);
  _generator=generator;
  _generator->attach(this);
}
void SaturationAlgorithm::setImmediateSimplificationEngine(ImmediateSimplificationEngineSP immediateSimplifier)
{
  ASS(!_immediateSimplifier);
  _immediateSimplifier=immediateSimplifier;
  _immediateSimplifier->attach(this);
}

void SaturationAlgorithm::addForwardSimplifierToFront(ForwardSimplificationEngineSP fwSimplifier)
{
  FwSimplList::push(fwSimplifier, _fwSimplifiers);
  fwSimplifier->attach(this);
}

void SaturationAlgorithm::addBackwardSimplifierToFront(BackwardSimplificationEngineSP bwSimplifier)
{
  BwSimplList::push(bwSimplifier, _bwSimplifiers);
  bwSimplifier->attach(this);
}

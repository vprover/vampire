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

using namespace Lib;
using namespace Kernel;
using namespace Shell;
using namespace Saturation;


SaturationAlgorithm::SaturationAlgorithm(PassiveClauseContainerSP passiveContainer,
	LiteralSelectorSP selector)
: _imgr(this), _passive(passiveContainer), _fwSimplifiers(0), _bwSimplifiers(0), _selector(selector)
{
  _unprocessed=new UnprocessedClauseContainer();
  _active=new ActiveClauseContainer();

  _active->attach(this);
  _passive->attach(this);

#if VDEBUG
//  _active->addedEvent.subscribe(this,&SaturationAlgorithm::onActiveAdded);
//  _passive->addedEvent.subscribe(this,&SaturationAlgorithm::onPassiveAdded);
//  _passive->removedEvent.subscribe(this,&SaturationAlgorithm::onPassiveRemoved);
//  _unprocessed->addedEvent.subscribe(this,&SaturationAlgorithm::onUnprocessedAdded);
//  _unprocessed->removedEvent.subscribe(this,&SaturationAlgorithm::onUnprocessedRemoved);
//  _unprocessed->selectedEvent.subscribe(this,&SaturationAlgorithm::onUnprocessedSelected);
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

  //TODO: perform splitting

  _unprocessed->add(cl);
}

bool SaturationAlgorithm::forwardSimplify(Clause* cl)
{
  CALL("SaturationAlgorithm::forwardSimplify");

  BDD* bdd=BDD::instance();

  if(!getLimits()->fulfillsLimits(cl)) {
    return false;
  }

  FwSimplList::Iterator fsit(_fwSimplifiers);
  while(fsit.hasNext()) {
    ForwardSimplificationEngine* fse=fsit.next().ptr();

    bool keep;
    ClauseIterator replacements;
    ClauseIterator premises;
    fse->perform(cl, keep, replacements, premises);
    if(keep) {
      ASS(!replacements.hasNext());
      continue;
    }

    BDDNode* premiseProp=bdd->getFalse();
    while(premises.hasNext()) {
      premiseProp=bdd->disjunction(premiseProp, premises.next()->prop());
    }


    BDDNode* replacementProp;
    if(replacements.hasNext()) {
      replacementProp=bdd->disjunction(cl->prop(), premiseProp);
    }
    while(replacements.hasNext()) {
      Clause* addCl=replacements.next();
      addCl->setProp(replacementProp);
      addUnprocessedClause(addCl);
    }

    cl->setProp(bdd->conjunction(cl->prop(), premiseProp));

    if(bdd->isTrue(cl->prop())) {
      return false;
    }
  }
  return true;
}

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

      BDDNode* replacementProp;
      if(srec.replacements.hasNext()) {
	replacementProp=bdd->disjunction(cl->prop(), redundant->prop());
      }
      while(srec.replacements.hasNext()) {
	Clause* addCl=srec.replacements.next();
	addCl->setProp(replacementProp);
	addUnprocessedClause(addCl);
      }

      redundant->setProp(bdd->xOrNonY(redundant->prop(), cl->prop()));

      if(bdd->isTrue(redundant->prop())) {
	switch(redundant->store()) {
	case Clause::PASSIVE:
	  _passive->remove(redundant);
	  break;
	case Clause::ACTIVE:
	  _active->remove(redundant);
	  break;
	default:
	  ASSERTION_VIOLATION;
	}
      }

    }
  }
}

void SaturationAlgorithm::activate(Clause* cl)
{
  CALL("SaturationAlgorithm::activate");

  _selector->select(cl);
  _active->add(cl);
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
      prop=bdd->disjunction(prop, premCl->prop());
    }

    if(bdd->isTrue(prop)) {
      continue;
    }

    genCl->setProp(prop);

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

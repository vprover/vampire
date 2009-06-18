/**
 * @file SaturationAlgorithm.cpp
 * Implementing SaturationAlgorithm class.
 */

#include "../Lib/Environment.hpp"
#include "../Lib/Metaiterators.hpp"
#include "../Lib/Timer.hpp"
#include "../Lib/VirtualIterator.hpp"
#include "../Kernel/BDD.hpp"
#include "../Kernel/Clause.hpp"
#include "../Kernel/Inference.hpp"
#include "../Kernel/InferenceStore.hpp"
#include "../Kernel/LiteralSelector.hpp"
#include "../Kernel/MLVariant.hpp"
#include "../Shell/Options.hpp"
#include "../Shell/Statistics.hpp"

#include "SaturationAlgorithm.hpp"



using namespace Lib;
using namespace Kernel;
using namespace Shell;
using namespace Saturation;

#define REPORT_CONTAINERS 0
#define REPORT_FW_SIMPL 0
#define REPORT_BW_SIMPL 0
#define TOTAL_SIMPLIFICATION_ONLY 1
#define FW_DEMODULATION_FIRST 1

SaturationAlgorithm::SaturationAlgorithm(PassiveClauseContainerSP passiveContainer,
	LiteralSelectorSP selector)
: _imgr(this), _passive(passiveContainer), _fwSimplifiers(0), _bwSimplifiers(0), _selector(selector)
{
  _performSplitting= env.options->splitting()!=Options::SPLIT_OFF;
  _someSplitting= env.options->splitting()!=Options::SPLIT_OFF;

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

  if(env.options->maxWeight()) {
    _limits.setLimits(-1,env.options->maxWeight());
  }
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

  _fwDemodulator->detach();
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


void SaturationAlgorithm::handleSaturationStart()
{
  _startTime=env.timer->elapsedMilliseconds();
}

int SaturationAlgorithm::elapsedTime()
{
  return env.timer->elapsedMilliseconds()-_startTime;
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

    if(env.options->sos() && cl->inputType()==Clause::AXIOM) {
      cl->setStore(Clause::ACTIVE);
      env.statistics->activeClauses++;
      _active->add(cl);
    } else {
      addUnprocessedClause(cl);
    }

    env.statistics->initialClauses++;
  }

  if(env.options->splitting()==Options::SPLIT_INPUT_ONLY) {
    _performSplitting=false;
  }
}

bool SaturationAlgorithm::isRefutation(Clause* c)
{
  CALL("SaturationAlgorithm::isRefutation");
  ASS(c->prop());

  BDD* bdd=BDD::instance();
  return c->isEmpty() && bdd->isFalse(c->prop());
}


class TotalSimplificationPerformer
: public ForwardSimplificationPerformer
{
public:
  TotalSimplificationPerformer(Clause* cl) : _cl(cl), _toAddLst(0) {}

  ~TotalSimplificationPerformer() { _toAddLst->destroy(); }

  void perform(Clause* premise, Clause* replacement)
  {
    CALL("TotalSimplificationPerformer::perform");
    ASS(_cl);
    ASS(willPerform(premise));

    BDD* bdd=BDD::instance();

    BDDNode* oldClProp=_cl->prop();

#if REPORT_FW_SIMPL
    cout<<"->>--------\n";
    if(premise) {
      cout<<":"<<(*premise)<<endl;
    }
    cout<<"-"<<(*_cl)<<endl;
#endif

    if(replacement) {
      replacement->setProp(oldClProp);
      InferenceStore::instance()->recordNonPropInference(replacement);
      ClauseList::push(replacement, _toAddLst);
    }

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

    BDD* bdd=BDD::instance();
    return bdd->isXOrNonYConstant(_cl->prop(), premise->prop(), true);
  }

  bool clauseKept()
  { return _cl; }

  ClauseIterator clausesToAdd()
  { return pvi( ClauseList::Iterator(_toAddLst) ); }
private:
  Clause* _cl;
  ClauseList* _toAddLst;
};

class PartialSimplificationPerformer
: public ForwardSimplificationPerformer
{
public:
  PartialSimplificationPerformer(Clause* cl) : _cl(cl), _toAddLst(0) {}

  ~PartialSimplificationPerformer() { _toAddLst->destroy(); }

  void perform(Clause* premise, Clause* replacement)
  {
    CALL("ForwardSimplificationPerformerImpl::perform");
    ASS(_cl);

    BDD* bdd=BDD::instance();

    BDDNode* oldClProp=_cl->prop();
    BDDNode* premiseProp = premise ? premise->prop() : bdd->getFalse();
    BDDNode* newClProp = bdd->xOrNonY(oldClProp, premiseProp);


#if REPORT_FW_SIMPL
    cout<<"->>--------\n";
    if(premise) {
      cout<<":"<<(*premise)<<endl;
    }
    cout<<"-"<<(*_cl)<<endl;
#endif


    if(replacement) {
      BDDNode* replacementProp=bdd->disjunction(oldClProp, premiseProp);
      if(!bdd->isTrue(replacementProp)) {
	replacement->setProp(replacementProp);
	InferenceStore::instance()->recordNonPropInference(replacement);
	ClauseList::push(replacement, _toAddLst);
      }
    }

    _cl->setProp(newClProp);
    InferenceStore::instance()->recordPropReduce(_cl, oldClProp, newClProp);

    if(bdd->isTrue(_cl->prop())) {
      _cl=0;
    }
#if REPORT_FW_SIMPL
    if(replacement) {
      cout<<"+"<<(*replacement)<<endl;
    }
    if(_cl) {
      cout<<">"<<(*_cl)<<endl;
      cout<<"^^^^^^^^^^^\n";
    } else {
      cout<<"removed\n";
      cout<<"^^^^^^^^^^^^\n";
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

#if REPORT_CONTAINERS
  cout<<"$$ Unprocessed adding: "<<(*cl)<<endl;
#endif

  env.statistics->generatedClauses++;

  BDD* bdd=BDD::instance();
  ASS(!bdd->isTrue(cl->prop()));

simplificationStart:
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
      InferenceStore::instance()->recordNonPropInference(cl);
    }
  } while(simplified);


#if FW_DEMODULATION_FIRST
  if(_fwDemodulator) {
    TotalSimplificationPerformer demPerformer(cl);
    _fwDemodulator->perform(cl, &demPerformer);
    if(!demPerformer.clauseKept()) {
      ClauseIterator rit=demPerformer.clausesToAdd();
      if(!rit.hasNext()) {
	//clause was demodulated into a tautology
	return;
      }
      cl=rit.next();

      ASS(!rit.hasNext());
      goto simplificationStart;
    }
  }
#endif

  ASS(!bdd->isTrue(cl->prop()));

//  static int scCounter=0;
//  scCounter++;
//  if(scCounter==100) {
//    scCounter=0;
//    if(_performSplitting && elapsedTime()>(env.options->timeLimitInDeciseconds()*5)) {
//      _performSplitting=false;
//    }
//  }

  if(_performSplitting) {
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
  } else {
    if(_someSplitting && cl->isEmpty()) {
      static Clause* emptyClause=0;
      if(emptyClause) {
	BDDNode* oldECProp=emptyClause->prop();
	BDDNode* newECProp=bdd->conjunction(oldECProp, cl->prop());
	emptyClause->setProp(newECProp);
	InferenceStore::instance()->recordMerge(emptyClause, oldECProp, cl, newECProp);

	if(isRefutation(emptyClause)) {
	  //Don't care about setting clause storage or anything, as
	  //we're done as soon as the saturation algorithm pops this
	  //clause from the unprocessed container.
	  _unprocessed->add(emptyClause);
	}
#if REPORT_CONTAINERS
	cout<<"%% Empty clause extended from: "<<bdd->toString(oldECProp)<<endl;
	cout<<"%% by: "<<bdd->toString(cl->prop())<<endl;
	cout<<"%% to: "<<bdd->toString(newECProp)<<endl;
#endif
	return;
      } else {
	emptyClause=cl;
      }
    }

    cl->setStore(Clause::UNPROCESSED);
    _unprocessed->add(cl);
  }
}

void SaturationAlgorithm::reanimate(Clause* cl)
{
  CALL("SaturationAlgorithm::reanimate");
  ASS_EQ(cl->store(), Clause::ACTIVE);

  ASS(!BDD::instance()->isTrue(cl->prop()));

  cl->setStore(Clause::REACTIVATED);
  _passive->add(cl);
}

bool SaturationAlgorithm::forwardSimplify(Clause* cl)
{
  CALL("SaturationAlgorithm::forwardSimplify");

  if(cl->store()==Clause::REACTIVATED) {
    return true;
  }

  if(!getLimits()->fulfillsLimits(cl)) {
    return false;
  }

#if TOTAL_SIMPLIFICATION_ONLY
  TotalSimplificationPerformer performer(cl);
#else
  PartialSimplificationPerformer performer(cl);
#endif

//#if FW_DEMODULATION_FIRST
//  FwSimplList::Iterator fsit(_fwSimplifiers);
//#else
  VirtualIterator<ForwardSimplificationEngineSP> fsit;
  if(_fwDemodulator) {
    fsit=pvi( getConcatenatedIterator(
	    FwSimplList::Iterator(_fwSimplifiers),
	    getSingletonIterator(_fwDemodulator)) );
  } else {
    fsit=pvi( FwSimplList::Iterator(_fwSimplifiers) );
  }
//#endif
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

//  if(cl->store()==Clause::REACTIVATED) {
//    return;
//  }

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
      BDDNode* newRedundantProp;

#if TOTAL_SIMPLIFICATION_ONLY
      if( !bdd->isXOrNonYConstant(oldRedundantProp, cl->prop(), true) ) {
	continue;
      }
      newRedundantProp=bdd->getTrue();
#else
      newRedundantProp=bdd->xOrNonY(oldRedundantProp, cl->prop());
      if( newRedundantProp==oldRedundantProp ) {
	continue;
      }
#endif

#if REPORT_BW_SIMPL
      cout<<"-<<--------\n";
      cout<<":"<<(*cl)<<endl;
      cout<<"-"<<(*redundant)<<endl;

      if(MLVariant::isVariant(cl, redundant)) {
	cout<<"Variant!!!\n";
      }
#endif

      //we must remove the redundant clause before adding its replacement,
      //as otherwise the redundant one might demodulate the replacement into
      //a tautology

      redundant->setProp(newRedundantProp);
      InferenceStore::instance()->recordPropReduce(redundant, oldRedundantProp, newRedundantProp);

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
      }
//      else if(redundant->store()==Clause::ACTIVE) {
//	reanimate(redundant);
//      }

      if(srec.replacements.hasNext()) {
	BDDNode* replacementProp=bdd->disjunction(oldRedundantProp, cl->prop());
	if(!bdd->isTrue(replacementProp)) {

	  while(srec.replacements.hasNext()) {
	    Clause* addCl=srec.replacements.next();
	    addCl->setProp(replacementProp);
	    InferenceStore::instance()->recordNonPropInference(addCl);
#if REPORT_BW_SIMPL
	    cout<<"+"<<(*addCl)<<endl;
#endif
	    addUnprocessedClause(addCl);
	  }
	}
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

    InferenceStore::instance()->recordNonPropInference(genCl);

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

void SaturationAlgorithm::setFwDemodulator(ForwardSimplificationEngineSP fwDemodulator)
{
  _fwDemodulator=fwDemodulator;
  fwDemodulator->attach(this);
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

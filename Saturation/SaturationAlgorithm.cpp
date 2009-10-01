/**
 * @file SaturationAlgorithm.cpp
 * Implementing SaturationAlgorithm class.
 */

#include "../Lib/Environment.hpp"
#include "../Lib/Metaiterators.hpp"
#include "../Lib/Stack.hpp"
#include "../Lib/Timer.hpp"
#include "../Lib/VirtualIterator.hpp"

#include "../Kernel/BDD.hpp"
#include "../Kernel/Clause.hpp"
#include "../Kernel/Inference.hpp"
#include "../Kernel/InferenceStore.hpp"
#include "../Kernel/LiteralSelector.hpp"
#include "../Kernel/MLVariant.hpp"
#include "../Kernel/Unit.hpp"
#include "../Kernel/FormulaUnit.hpp"
#include "../Kernel/SubformulaIterator.hpp"

#include "../Shell/Options.hpp"
#include "../Shell/Statistics.hpp"

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
/** Perform simplification on a clause only if it leads to its deletion
 * (i.e. propositional part of the premise implies propositional part
 * of the simplified clause. */
#define TOTAL_SIMPLIFICATION_ONLY 1
/** Perform forward demodulation before a clause is passed to splitting */
#define FW_DEMODULATION_FIRST 1

/** Always split out propositional literals to the propositional part of the clause */
#define PROPOSITIONAL_PREDICATES_ALWAYS_TO_BDD 1

/**
 * Create a SaturationAlgorithm object
 *
 * The @b passiveContainer object will be used as a passive clause container, and
 * @b selector object to select literals before clauses are activated.
 */
SaturationAlgorithm::SaturationAlgorithm(PassiveClauseContainerSP passiveContainer,
	LiteralSelectorSP selector)
: _imgr(this), _clauseActivationInProgress(false), _passive(passiveContainer), _fwSimplifiers(0), _bwSimplifiers(0), _selector(selector)
{
  _performSplitting= env.options->splitting()!=Options::RA_OFF;

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
    _limits.setLimits(-1,env.options->maxWeight());
  }

}

/**
 * Destroy the SaturationAlgorithm object
 */
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

/**
 * A function that is called when a clause is added to the active clause container.
 */
void SaturationAlgorithm::onActiveAdded(Clause* c)
{
#if REPORT_CONTAINERS
  cout<<"## Active added: "<<(*c)<<endl;
#endif

  if(env.options->showActive()) {
    cout<<"Active: "<<c->toTPTPString()<<endl;
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

  ASS(c->store()==Clause::ACTIVE || c->store()==Clause::REACTIVATED)

  if(c->store()==Clause::ACTIVE) {
    c->setStore(Clause::NONE);
  } else if(c->store()==Clause::REACTIVATED) {
    c->setStore(Clause::PASSIVE);
  }
#if VDEBUG
  else {
    ASSERTION_VIOLATION;
  }
#endif
}

/**
 * A function that is called when a clause is added to the passive clause container.
 */
void SaturationAlgorithm::onPassiveAdded(Clause* c)
{
#if REPORT_CONTAINERS
  cout<<"# Passive added: "<<(*c)<<endl;
#endif

  if(env.options->showPassive()) {
    cout<<"Passive: "<<c->toTPTPString()<<endl;
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
void SaturationAlgorithm::onNewClause(Clause* c)
{
  CALL("SaturationAlgorithm::onNewClause");

  if(env.options->showNew()) {
    cout<<"New: "<<c->toTPTPString()<<endl;
  }

#if !PROPOSITIONAL_PREDICATES_ALWAYS_TO_BDD
  if(c->isPropositional()) {
    onNewUsefulPropositionalClause(c);
  }
#endif
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
}

void SaturationAlgorithm::onSymbolElimination(Clause* c)
{
  CALL("SaturationAlgorithm::onSymbolElimination");
  ASS_EQ(c->color(),COLOR_TRANSPARENT);

  if(env.options->showSymbolElimination()) {
    cout<<"Symbol elimination: "<<c->toTPTPString()<<endl;
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
 * A function that is called as a first thing in the @b saturate() function.
 *
 * The @b saturate function is abstract and implemented by inheritors. It is therefore
 * up to them to call this function as they should.
 */
void SaturationAlgorithm::handleSaturationStart()
{
  _startTime=env.timer->elapsedMilliseconds();
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

  cl->setProp(BDD::instance()->getFalse());

  checkForPreprocessorSymbolElimination(cl);

#if PROPOSITIONAL_PREDICATES_ALWAYS_TO_BDD
  //put propositional predicates into BDD part
  cl=_propToBDD.simplify(cl);
#endif

  if(env.options->sos() && cl->inputType()==Clause::AXIOM) {
    addInputSOSClause(cl);
  } else {
    addUnprocessedClause(cl);
  }

  env.statistics->initialClauses++;
}

/**
 * Add an input set-of-support clause @b cl into the active container
 */
void SaturationAlgorithm::addInputSOSClause(Clause*& cl)
{
  CALL("SaturationAlgorithm::addInputSOSClause");
  ASS_EQ(cl->inputType(),Clause::AXIOM);

  onNewClause(cl);

  cl=doImmediateSimplification(cl);

  cl->setStore(Clause::ACTIVE);
  env.statistics->activeClauses++;
  _active->add(cl);
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

  if(env.options->splitting()==Options::RA_INPUT_ONLY) {
    _performSplitting=false;
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
  return c->isEmpty() && bdd->isFalse(c->prop());
}


void SaturationAlgorithm::checkForPreprocessorSymbolElimination(Clause* cl)
{
  CALL("SaturationAlgorithm::checkForPreprocessorSymbolElimination");

  if(!env.colorUsed || cl->color()!=COLOR_TRANSPARENT) {
    return;
  }

  //TODO: it might examine some parts of the proof-tree multiple times,
  //so perhaps some more caching could be used if it's too slow

  Color inputColor=COLOR_TRANSPARENT;

  static DHMap<Unit*, Color> inputFormulaColors;
  static Stack<Unit*> units;
  units.reset();
  units.push(cl);

  while(units.isNonEmpty()) {
    Unit* u=units.pop();
    if(u->inference()->rule()==Inference::INPUT ||
	    u->inference()->rule()==Inference::NEGATED_CONJECTURE) {
      Color uCol;
      if(u->isClause()) {
	uCol=static_cast<Clause*>(u)->color();
      } else if(!inputFormulaColors.find(u,uCol)){
	uCol=getFormulaColor(static_cast<FormulaUnit*>(u));
	inputFormulaColors.insert(u,uCol);
      }
      if(uCol!=COLOR_TRANSPARENT) {
#if VDEBUG
	inputColor=static_cast<Color>(inputColor|uCol);
	ASS_NEQ(inputColor, COLOR_INVALID);
#else
	inputColor=uCol;
	break;
#endif
      }
    } else {
      Inference::Iterator iit=cl->inference()->iterator();
      while(u->inference()->hasNext(iit)) {
        Unit* premUnit=u->inference()->next(iit);
        units.push(premUnit);
      }
    }
  }

  if(inputColor!=COLOR_TRANSPARENT) {
    onSymbolElimination(cl);
  }
}

Color SaturationAlgorithm::getFormulaColor(FormulaUnit* f)
{
  CALL("SaturationAlgorithm::getFormulaColor");

  SubformulaIterator si(f->formula());
  while(si.hasNext()) {
    Formula* f=si.next();
    if(f->connective()!=LITERAL) {
      continue;
    }

    if(f->literal()->color()!=COLOR_TRANSPARENT) {
      return f->literal()->color();
    }
  }
  return COLOR_TRANSPARENT;
}


/**
 * Class of @b ForwardSimplificationPerformer objects that
 * perform the forward simplification only if it leads to
 * deletion of the clause being simplified. (I.e. other
 * possibility would be to also perform simplifications that
 * only alter clause's BDD.)
 */
class SaturationAlgorithm::TotalSimplificationPerformer
: public ForwardSimplificationPerformer
{
public:
  TotalSimplificationPerformer(SaturationAlgorithm* sa, Clause* cl) : _sa(sa), _cl(cl), _toAddLst(0) {}

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

      if(premise) {
	Color premColor=static_cast<Color>(_cl->color() | premise->color());
	ASS_NEQ(premColor, COLOR_INVALID);
	if(premColor!=COLOR_TRANSPARENT && replacement->color()==COLOR_TRANSPARENT) {
	  _sa->onSymbolElimination(replacement);
	}
      }
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

  ClauseIterator clausesToAdd()
  { return pvi( ClauseList::Iterator(_toAddLst) ); }
private:
  SaturationAlgorithm* _sa;
  Clause* _cl;
  ClauseList* _toAddLst;
};

/**
 * Class of @b ForwardSimplificationPerformer objects that
 * perform the forward simplification anytime it is possible.
 * I.e. not only if it leads to the deletion of the clause
 * being simplified.
 */
class SaturationAlgorithm::PartialSimplificationPerformer
: public ForwardSimplificationPerformer
{
public:
  PartialSimplificationPerformer(SaturationAlgorithm* sa, Clause* cl) : _sa(sa), _cl(cl), _toAddLst(0) {}

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

      if(premise) {
	Color premColor=static_cast<Color>(_cl->color() | premise->color());
	ASS_NEQ(premColor, COLOR_INVALID);
	if(premColor!=COLOR_TRANSPARENT && replacement->color()==COLOR_TRANSPARENT) {
	  _sa->onSymbolElimination(replacement);
	}
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

  bool willPerform(Clause* premise)
  {
    CALL("PartialSimplificationPerformer::willPerform");
    ASS(_cl);

    if(!premise) {
      return true;
    }

    if( (_cl->color()|premise->color())==COLOR_INVALID ) {
      return false;
    }

    return true;
  }

  bool clauseKept()
  { return _cl; }

  ClauseIterator clausesToAdd()
  { return pvi( ClauseList::Iterator(_toAddLst) ); }
private:
  SaturationAlgorithm* _sa;
  Clause* _cl;
  ClauseList* _toAddLst;
};

Clause* SaturationAlgorithm::doImmediateSimplification(Clause* cl)
{
  CALL("SaturationAlgorithm::doImmediateSimplification");

  BDDNode* prop=cl->prop();
  bool simplified;
  do {
    Clause* simplCl=_immediateSimplifier->simplify(cl);
    if(simplCl==0) {
      return 0;
    }
    simplified=simplCl!=cl;
    if(simplified) {
      ASS_EQ(simplCl->prop(), 0);
      simplCl->setProp(prop);
      InferenceStore::instance()->recordNonPropInference(simplCl);

      if(cl->color()!=COLOR_TRANSPARENT && simplCl->color()==COLOR_TRANSPARENT) {
	onSymbolElimination(simplCl);
      }

      cl=simplCl;

      onNewClause(cl);
    }
  } while(simplified);

  return cl;
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

simplificationStart:

  onNewClause(cl);

  cl=doImmediateSimplification(cl);


#if FW_DEMODULATION_FIRST
  if(_fwDemodulator) {
    TotalSimplificationPerformer demPerformer(this, cl);
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

  if(_performSplitting && !cl->isEmpty()) {
    ClauseIterator newComponents;
    ClauseIterator modifiedComponents;
    _splitter.doSplitting(cl, newComponents, modifiedComponents);
    Color origColor=cl->color();
    while(newComponents.hasNext()) {
      Clause* comp=newComponents.next();
      ASS_EQ(comp->store(), Clause::NONE);
      ASS(!bdd->isTrue(comp->prop()));

      if(comp!=cl) {
	onNewClause(comp);
	if(origColor!=COLOR_TRANSPARENT && comp->color()==COLOR_TRANSPARENT) {
	  onSymbolElimination(comp);
	}
      }

      addUnprocessedFinalClause(comp);
    }
    while(modifiedComponents.hasNext()) {
      Clause* comp=modifiedComponents.next();

      if(origColor!=COLOR_TRANSPARENT && comp->color()==COLOR_TRANSPARENT) {
	onSymbolElimination(comp);
      }

      ASS(!bdd->isTrue(comp->prop()));
      if(comp->store()==Clause::ACTIVE) {
        if(!comp->isEmpty()) { //don't reanimate empty clause
          reanimate(comp);
        } else {
          ASS(!isRefutation(comp));
        }
      } else if(comp->store()==Clause::NONE) {
        addUnprocessedFinalClause(comp);
      } else {
	ASS(comp->store()==Clause::PASSIVE ||
		comp->store()==Clause::REACTIVATED ||
		comp->store()==Clause::UNPROCESSED);
      }
      onNewClause(comp);
    }
  } else {
    addUnprocessedFinalClause(cl);
  }
}

/**
 * Add clause @b cl to the unprocessed container without performing any
 * simplifications. Only clauses with empty non-propositional part are
 * dealt with specially by the @b handleEmptyClause function.
 */
void SaturationAlgorithm::addUnprocessedFinalClause(Clause* cl)
{
  CALL("SaturationAlgorithm::addUnprocessedFinalClause");


  if( cl->isEmpty() ) {
    cl=handleEmptyClause(cl);
    if(!cl) {
      return;
    }
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
Clause* SaturationAlgorithm::handleEmptyClause(Clause* cl)
{
  CALL("SaturationAlgorithm::handleEmptyClause");
  ASS(cl->isEmpty());

  BDD* bdd=BDD::instance();

  if(bdd->isFalse(cl->prop())) {
    return cl;
  }

  if(env.options->satSolverForEmptyClause()) {
    static BDDConjunction ecProp;
    static Stack<InferenceStore::ClauseSpec> emptyClauses;

#if PROPOSITIONAL_PREDICATES_ALWAYS_TO_BDD
    onNewUsefulPropositionalClause(cl);
#endif
    ecProp.addNode(cl->prop());
    if(ecProp.isFalse()) {
      InferenceStore::instance()->recordMerge(cl, cl->prop(), emptyClauses.begin(),
	      emptyClauses.size(), bdd->getFalse());
      cl->setProp(bdd->getFalse());
      onNewUsefulPropositionalClause(cl);
      return cl;
    } else {
      emptyClauses.push(InferenceStore::getClauseSpec(cl));
      return 0;
    }
  } else {
    static Clause* accumulator=0;
    if(accumulator==0) {
      accumulator=cl;
#if PROPOSITIONAL_PREDICATES_ALWAYS_TO_BDD
      onNewUsefulPropositionalClause(cl);
#endif
      return 0;
    }
    BDDNode* newProp=bdd->conjunction(accumulator->prop(), cl->prop());
#if PROPOSITIONAL_PREDICATES_ALWAYS_TO_BDD
    if(newProp!=accumulator->prop()) {
      onNewUsefulPropositionalClause(cl);
    }
#endif
    if(bdd->isFalse(newProp)) {
      InferenceStore::instance()->recordMerge(cl, cl->prop(), accumulator, newProp);
      cl->setProp(newProp);
      onNewUsefulPropositionalClause(cl);
      return cl;
    }
    if(newProp!=accumulator->prop()) {
      InferenceStore::instance()->recordMerge(accumulator, accumulator->prop(), cl, newProp);
      accumulator->setProp(newProp);
    } else {
      env.statistics->subsumedEmptyClauses++;
      if(env.options->emptyClauseSubsumption()) {
	performEmptyClauseSubsumption(cl, accumulator->prop());
      }
    }
    return 0;
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
void SaturationAlgorithm::performEmptyClauseSubsumption(Clause* cl, BDDNode* emptyClauseProp)
{
  CALL("SaturationAlgorithm::performEmptyClauseSubsumption");
  ASS(cl->isEmpty());

  BDD* bdd=BDD::instance();

  static Stack<Clause*> parentsToCheck;
  ASS(parentsToCheck.isEmpty());
  parentsToCheck.push(cl);

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
      removeBackwardSimplifiedClause(par);
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

  if(cl->store()==Clause::REACTIVATED) {
    return true;
  }

  if(!getLimits()->fulfillsLimits(cl)) {
    env.statistics->discardedNonRedundantClauses++;
    return false;
  }

#if TOTAL_SIMPLIFICATION_ONLY
  TotalSimplificationPerformer performer(this, cl);
#else
  PartialSimplificationPerformer performer(this, cl);
#endif

  VirtualIterator<ForwardSimplificationEngineSP> fsit;
  if(_fwDemodulator) {
    fsit=pvi( getConcatenatedIterator(
	    FwSimplList::Iterator(_fwSimplifiers),
	    getSingletonIterator(_fwDemodulator)) );
  } else {
    fsit=pvi( FwSimplList::Iterator(_fwSimplifiers) );
  }

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

/**
 * The the backward simplification with the clause @b cl.
 */
void SaturationAlgorithm::backwardSimplify(Clause* cl)
{
  CALL("SaturationAlgorithm::backwardSimplify");

//  if(cl->store()==Clause::REACTIVATED) {
//    return;
//  }

  static Stack<Clause*> replacementsToAdd;

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

      replacementsToAdd.reset();

      if(srec.replacements.hasNext()) {
	BDDNode* replacementProp=bdd->disjunction(oldRedundantProp, cl->prop());
	if(!bdd->isTrue(replacementProp)) {

	  Color premColor=static_cast<Color>(redundant->color()|cl->color());
	  ASS_NEQ(premColor, COLOR_INVALID);

	  while(srec.replacements.hasNext()) {
	    Clause* addCl=srec.replacements.next();
	    addCl->setProp(replacementProp);
	    InferenceStore::instance()->recordNonPropInference(addCl);
	    replacementsToAdd.push(addCl);
#if REPORT_BW_SIMPL
	    cout<<"+"<<(*addCl)<<endl;
#endif

	    if(premColor!=COLOR_TRANSPARENT && addCl->color()==COLOR_TRANSPARENT) {
	      onSymbolElimination(addCl);
	    }
	  }
	}
      }


      //we must remove the redundant clause before adding its replacement,
      //as otherwise the redundant one might demodulate the replacement into
      //a tautology

      redundant->setProp(newRedundantProp);
      InferenceStore::instance()->recordPropReduce(redundant, oldRedundantProp, newRedundantProp);

      if(bdd->isTrue(newRedundantProp)) {
	removeBackwardSimplifiedClause(redundant);
#if REPORT_BW_SIMPL
	cout<<"removed\n";
#endif
      }

      unsigned addCnt=replacementsToAdd.size();
      for(unsigned i=0;i<addCnt;i++) {
	addUnprocessedClause(replacementsToAdd[i]);
      }
      replacementsToAdd.reset();


#if REPORT_BW_SIMPL
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
void SaturationAlgorithm::removeBackwardSimplifiedClause(Clause* cl)
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
    _active->remove(cl);
    break;
  case Clause::REACTIVATED:
    _passive->remove(cl);
    _active->remove(cl);
    break;
  default:
    ASSERTION_VIOLATION;
  }
  cl->setStore(Clause::NONE);
}

/**
 * Add clause @b c to the passive container
 */
void SaturationAlgorithm::addToPassive(Clause* c)
{
  CALL("SaturationAlgorithm::addToPassive");

  ASS_EQ(c->store(), Clause::UNPROCESSED);
  c->setStore(Clause::PASSIVE);
  env.statistics->passiveClauses++;

  _passive->add(c);
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

  _clauseActivationInProgress=true;

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
    Color premColor=COLOR_TRANSPARENT;
    while(genCl->inference()->hasNext(iit)) {
      Unit* premUnit=genCl->inference()->next(iit);
      ASS(premUnit->isClause());
      Clause* premCl=static_cast<Clause*>(premUnit);

      premColor = static_cast<Color>(premColor | premCl->color());

      prop=bdd->disjunction(prop, premCl->prop());
    }

    genCl->setProp(prop);
#if REPORT_CONTAINERS
    cout<<"G "<<(*genCl)<<endl;
#endif

    if(bdd->isTrue(prop)) {
      continue;
    }
    InferenceStore::instance()->recordNonPropInference(genCl);

    ASS_NEQ(premColor, COLOR_INVALID);
    if(premColor!=COLOR_TRANSPARENT && genCl->color()==COLOR_TRANSPARENT) {
      onSymbolElimination(genCl);
    }

    addUnprocessedClause(genCl);
  }

  _clauseActivationInProgress=false;

  //now we remove clauses that could not be removed during the clause activation process
  while(_postponedClauseRemovals.isNonEmpty()) {
    Clause* cl=_postponedClauseRemovals.pop();
    if(cl->store()!=Clause::ACTIVE &&
	cl->store()!=Clause::PASSIVE &&
	cl->store()!=Clause::REACTIVATED) {
      continue;
    }
    removeBackwardSimplifiedClause(cl);
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
 * Assign forward simplifier object to perform forward demodulation
 *
 * A zero smart pointer can be passed as argument to dissable
 * forward demodulation.
 */
void SaturationAlgorithm::setFwDemodulator(ForwardSimplificationEngineSP fwDemodulator)
{
  _fwDemodulator=fwDemodulator;
  fwDemodulator->attach(this);
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

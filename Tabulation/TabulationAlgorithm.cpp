/**
 * @file TabulationAlgorithm.cpp
 * Implements class TabulationAlgorithm.
 */

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/Environment.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Inference.hpp"
#include "Kernel/Problem.hpp"

#include "Inferences/TautologyDeletionISE.hpp"

#include "Shell/EqResWithDeletion.hpp"
#include "Shell/Options.hpp"
#include "Shell/Refutation.hpp"
#include "Shell/Statistics.hpp"

#include "TabulationAlgorithm.hpp"


namespace Tabulation
{

TabulationAlgorithm::TabulationAlgorithm(Problem& prb, const Options& opt)
: MainLoop(prb, opt), _goalContainer(opt), _gp(*this), _producer(*this),
  _instatiateProducingRules(opt.tabulationInstantiateProducingRules())
{
  CALL("TabulationAlgorithm::TabulationAlgorithm");

  _ise = createISE(prb, opt);

  _goalContainer.setAgeWeightRatio(
      opt.tabulationGoalAgeRatio(),opt.tabulationGoalWeightRatio());

  _refutation = 0;

  LOG("tab","TA created");
}

void TabulationAlgorithm::init()
{
  CALL("TabulationAlgorithm::init");

  LOG("tab","TA init");

  ClauseIterator cit = _prb.clauseIterator();

  while(cit.hasNext()) {
    Clause* cl = simplifyInputClause(cit.next());
    if(!cl) {
      continue;
    }
    if(isRefutation(cl)) {
      _refutation = cl;
      return;
    }
    cl->incRefCnt();
    cl->setSelected(cl->length());
    _theoryContainer.add(cl);
    if(cl->inputType()==Unit::AXIOM) {
      LOG("tab","TA added theory"<<(*cl));
    }
    else {
      if(cl->length()==1) {
        addLemma(cl);
      }
      else {
        addProducingRule(cl); //this is what will make us successfully terminate
      }
      addGoal(cl);
    }
  }
}

Clause* TabulationAlgorithm::simplifyInputClause(Clause* cl)
{
  CALL("TabulationAlgorithm::simplifyInputClause");

  static EqResWithDeletion erwd;

  cl = erwd.apply(cl);
  return _ise->simplify(cl);
}


void TabulationAlgorithm::addGoal(Clause* cl)
{
  CALL("TabulationAlgorithm::addGoal");

  cl->setStore(Clause::PASSIVE);
  _goalContainer.add(cl);
  LOG("tab","A added goal "<<cl->toString());
  RSTAT_CTR_INC("goal cnt");
}

void TabulationAlgorithm::addLemma(Clause* cl)
{
  CALL("TabulationAlgorithm::addLemma");
  ASS_EQ(cl->length(), 1);

  LOG("tab","A added lemma "<<cl->toString());
  if(cl->selected()==0) {
    Clause* cl0 = cl;
    cl = Clause::fromIterator(Clause::Iterator(*cl0), cl0->inputType(),
                              new Inference1(Inference::REORDER_LITERALS, cl0));
    cl->setSelected(1);
    cl->setAge(cl0->age());
  }

  cl->incRefCnt();

  RSTAT_CTR_INC("lemma cnt");

  _producer.onLemma(cl);
  _gp.onLemma(cl);
}

void TabulationAlgorithm::selectGoalLiteral(Clause*& cl)
{
  CALL("TabulationAlgorithm::selectGoalLiteral");

  unsigned clen = cl->length();
  ASS_G(clen,0);

  Literal* selected = 0;
  if(clen==1) {
    selected = (*cl)[0];
  }
  else {
    Clause::Iterator cit(*cl);
    while(cit.hasNext()) {
      Literal* lit = cit.next();
      if(_glContainer.isSubsumed(lit)) {
	selected = lit;
	break;
      }
    }
  }
  if(!selected) {
    Clause::Iterator cit(*cl);
    ALWAYS(cit.hasNext());
    selected = cit.next();
    unsigned selUnifCnt = _theoryContainer.getIndex()->getUnificationCount(selected, true);

    while(cit.hasNext()) {
      Literal* lit = cit.next();
      unsigned litUnifCnt = _theoryContainer.getIndex()->getUnificationCount(lit, true);
      if(litUnifCnt<selUnifCnt) {
        selUnifCnt = litUnifCnt;
        selected = lit;
      }
    }
    RSTAT_MCTR_INC("selected literal unifier count", selUnifCnt);
  }



  if(cl->selected()!=1 || (*cl)[0]!=selected) {
    Clause* cl2 = Clause::fromIterator(Clause::Iterator(*cl), cl->inputType(),
	new Inference1(Inference::REORDER_LITERALS, cl));
    unsigned selIdx = cl->getLiteralPosition(selected);
    if(selIdx!=0) {
      swap((*cl2)[0], (*cl2)[selIdx]);
      cl2->notifyLiteralReorder();
    }
    cl2->setSelected(1);
    cl2->setAge(cl->age());
    cl = cl2;
  }
  ASS_EQ((*cl)[0],selected);
}

Clause* TabulationAlgorithm::removeDuplicateLiterals(Clause* cl)
{
  CALL("TabulationAlgorithm::removeDuplicateLiterals");

  static DuplicateLiteralRemovalISE dupLitRemover;

  Clause* res = dupLitRemover.simplify(cl);
  ASS(res);
  ASS(cl->isEmpty() || !res->isEmpty());
  return res;
}

bool TabulationAlgorithm::isSimpleTautology(Clause* cl)
{
  CALL("TabulationAlgorithm::isSimpleTautology");

  static TautologyDeletionISE tautDeletion(false);

  return tautDeletion.simplify(cl)==0;
}

/**
 * Return a goal with the literals subsumed by other goal literals removed,
 * or 0 if all are subsumed.
 */
Clause* TabulationAlgorithm::processSubsumedGoalLiterals(Clause* goal)
{
  CALL("TabulationAlgorithm::processSubsumedGoalLiterals");

  static LiteralStack lits;
  lits.reset();
  Clause::Iterator cit(*goal);
  while(cit.hasNext()) {
    Literal* lit = cit.next();
    if(_glContainer.isSubsumed(lit)) {
      LOG("tab","A subsumed goal literal "<<lit->toString()<<" in goal "<<goal->toString());
      RSTAT_CTR_INC("subsumed goal literals removed");
      continue;
    }
    lits.push(lit);
  }
  unsigned  removedCnt = goal->length() - lits.size();
  if(removedCnt==0) {
    return goal;
  }

  if(lits.size()==0) {
    return 0;
  }

  //TODO: create proper inference
  Clause* res = Clause::fromStack(lits, Unit::CONJECTURE,
      new Inference(Inference::NEGATED_CONJECTURE));

  int newAge = goal->age() + removedCnt;
//  int newAge = goal->age();
  res->setAge(newAge);
  return res;
}

Clause* TabulationAlgorithm::generateGoal(Clause* cl, Literal* resolved, int parentGoalAge, ResultSubstitution* subst, bool result)
{
  CALL("TabulationAlgorithm::generateGoal");

  static LiteralStack lits;
  lits.reset();
  Clause::Iterator cit(*cl);
  while(cit.hasNext()) {
    Literal* lit = cit.next();
    if(lit==resolved) {
      continue;
    }
    if(subst) {
      lit = subst->apply(lit, result);
    }
    lits.push(lit);
  }
  if(lits.size()!=cl->length()-1) {
    Refutation r(cl, true);
    r.output(cout);
  }
  ASS_REP2(lits.size()==cl->length()-1, cl->toString(), resolved->toString());

  //TODO: create proper inference
  Clause* res = Clause::fromStack(lits, Unit::CONJECTURE,
      new Inference(Inference::NEGATED_CONJECTURE));

  int newAge = max(cl->age(), parentGoalAge)+1;
  res->setAge(newAge);

  res = removeDuplicateLiterals(res);

  return res;
}


void TabulationAlgorithm::addProducingRule(Clause* cl, Literal* head, ResultSubstitution* subst, bool result)
{
  CALL("TabulationAlgorithm::addProducingRule");


  bool freshClause = false;

  if(subst && _instatiateProducingRules) {
    cl = GoalProducer::makeInstance(cl, *subst, result);
    cl = removeDuplicateLiterals(cl);
    head = subst->apply(head, result);
  }

  RuleSpec spec(cl, head); //head may be zero

  if(!_addedProducingRules.insert(spec)) {
    RSTAT_CTR_INC("producing rules repeated");
    return;
  }

  if(isSimpleTautology(cl)) {
    RSTAT_CTR_INC("producing rule simple tautologies");
    return;
  }


  unsigned clen = cl->length();
  ASS_G(clen,0);
  if(head && clen==1) {
    ASS((*cl)[0]==head);
    addLemma(cl);
    return;
  }

  bool wellSet = (!head && cl->selected()==clen)
      || (head && cl->selected()==clen-1 && (*cl)[clen-1]==head);
  if(!wellSet && !freshClause) {
    Clause* cl0 = cl;
    cl = Clause::fromIterator(Clause::Iterator(*cl), Unit::ASSUMPTION,
	  new Inference1(Inference::REORDER_LITERALS, cl));
    cl->setAge(cl0->age());
  }

  if(!wellSet) {
    if(head) {
      unsigned headIdx = cl->getLiteralPosition(head);
      if(headIdx!=clen-1) {
	swap((*cl)[headIdx], (*cl)[clen-1]);
	cl->notifyLiteralReorder();
      }
      cl->setSelected(clen-1);
    }
    else {
      cl->setSelected(clen);
    }
  }
  ASS(!head || (*cl)[clen-1]==head);

  cl->incRefCnt();
  RSTAT_CTR_INC("producing rules added");
  _producer.addRule(cl);
}

void TabulationAlgorithm::addGoalProducingRule(Clause* oldGoal)
{
  CALL("TabulationAlgorithm::addGoalProducingRule");
  ASS_EQ(oldGoal->selected(), 1);

  if(oldGoal->length()==1) {
    return;
  }

  Literal* selected = (*oldGoal)[0];
  Literal* activator = Literal::complementaryLiteral(selected);
  Clause* newGoal = generateGoal(oldGoal, selected);

  newGoal = processSubsumedGoalLiterals(newGoal);
  if(newGoal) {
    _gp.addRule(newGoal, activator);
    RSTAT_CTR_INC("goal producing rules");
  }
  else {
    RSTAT_CTR_INC("goal producing rules skipped due to subsumption");
  }
}

void TabulationAlgorithm::processGoal(Clause* cl)
{
  CALL("TabulationAlgorithm::processGoal");
  ASS_G(cl->length(),0);
  ASS_EQ(cl->store(), Clause::PASSIVE);

  LOG("tab","A processing goal "<<cl->toString());

  selectGoalLiteral(cl);
  ASS_EQ(cl->selected(),1);

  addGoalProducingRule(cl);

  Literal* selLit = (*cl)[0];
  if(_glContainer.isSubsumed(selLit)) {
    RSTAT_CTR_INC("goals with subsumed selected literals");
    cl->setStore(Clause::NONE);
    return;
  }

  _glContainer.add(selLit);

  RSTAT_CTR_INC("goals triggering theory unifications");
  SLQueryResultIterator qrit = _theoryContainer.getIndex()->getUnifications(selLit, true, true);
  while(qrit.hasNext()) {
    RSTAT_CTR_INC("goals triggering theory unifications - found");
    SLQueryResult qres = qrit.next();

    if(qres.clause->length()==1) {
      RSTAT_CTR_INC("goals triggering theory unifications - found lemmas");
      addLemma(qres.clause);
      continue;
    }
    RSTAT_CTR_INC("goals triggering theory unifications - found rules");
    LOG("tab","A generating goal from: "<<qres.clause->toString());
    Clause* newGoal = generateGoal(qres.clause, qres.literal, cl->age(), qres.substitution.ptr(), true);
    addGoal(newGoal);
    addProducingRule(qres.clause, qres.literal, qres.substitution.ptr(), true);
  }
  LOG("tab","A goal processed: "<<cl->toString());
  cl->setStore(Clause::NONE);
  //here cl may be deleted
}


MainLoopResult TabulationAlgorithm::runImpl()
{
  CALL("TabulationAlgorithm::runImpl");

  LOG("tab","TA runImpl");

  if(_refutation) {
    return MainLoopResult(Statistics::REFUTATION, _refutation);
  }

  int lemmaRatio = _opt.tabulationLemmaRatio();
  int goalRatio = _opt.tabulationGoalRatio();
  int balance = 0;

  while(_producer.hasLemma() || !_goalContainer.isEmpty()) {
    if(balance>0) {
      balance-=goalRatio;
      if(_producer.hasLemma()) {
	RSTAT_CTR_INC("processed lemmas");
	_producer.processLemma();
      }
    }
    else {
      balance+=lemmaRatio;
      if(!_goalContainer.isEmpty()) {
	RSTAT_CTR_INC("processed goals");
	Clause* goal = _goalContainer.popSelected();
	processGoal(goal);
      }
    }

    _producer.onSafePoint();

    env -> checkTimeSometime<20>();
  }

  return MainLoopResult(Statistics::UNKNOWN);
}


}

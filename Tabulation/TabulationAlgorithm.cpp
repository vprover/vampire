/**
 * @file TabulationAlgorithm.cpp
 * Implements class TabulationAlgorithm.
 */

#include "Lib/VirtualIterator.hpp"

#include "Kernel/Inference.hpp"

#include "Shell/Statistics.hpp"

#include "TabulationAlgorithm.hpp"

namespace Tabulation
{

TabulationAlgorithm::TabulationAlgorithm()
{
  CALL("TabulationAlgorithm::TabulationAlgorithm");

  _ise = createISE();

  _refutation = 0;
}

void TabulationAlgorithm::addInputClauses(ClauseIterator cit)
{
  CALL("TabulationAlgorithm::addInputClauses");

  while(cit.hasNext()) {
    Clause* cl = simplifyClause(cit.next());
    if(!cl) {
      continue;
    }
    if(isRefutation(cl)) {
      _refutation = cl;
      return;
    }
    if(cl->inputType()==Unit::AXIOM) {
      cl->setSelected(cl->length());
      _theoryContainer.add(cl);
    }
    else {
      addProducingRule(cl); //this is what will make us successfully terminate
      addGoal(cl);
    }
  }
}

void TabulationAlgorithm::addGoal(Clause* cl)
{
  CALL("TabulationAlgorithm::addGoal");

  _goalContainer.add(cl);
}

void TabulationAlgorithm::selectGoalLiteral(Clause* cl)
{
  CALL("TabulationAlgorithm::selectGoalLiteral");
  ASS_G(cl->length(),0);

  //TODO: proper selection
  cl->setSelected(1);
}

Clause* TabulationAlgorithm::simplifyClause(Clause* cl)
{
  CALL("TabulationAlgorithm::simplifyClause");

  return _ise->simplify(cl);
}

Clause* TabulationAlgorithm::generateGoal(Clause* cl, Literal* resolved, int parentGoalAge)
{
  CALL("TabulationAlgorithm::generateGoal");

  static LiteralStack lits;
  lits.reset();
  lits.loadFromIterator(Clause::Iterator(*cl));
  lits.remove(resolved);
  ASS_EQ(lits.size(), cl->length()-1);

  //TODO: create proper inference
  Clause* res = Clause::fromStack(lits, Unit::CONJECTURE,
      new Inference(Inference::NEGATED_CONJECTURE));

  int newAge = max(cl->age(), parentGoalAge)+1;
  res->setAge(newAge);
  return res;
}


void TabulationAlgorithm::addProducingRule(Clause* cl0, Literal* head)
{
  CALL("TabulationAlgorithm::addProducingRule");

  unsigned clen = cl0->length();
  ASS_G(clen,0);
  ASS(!head || clen>1);

  Clause* cl = cl0;
  bool canReuse = (!head && cl->selected()==clen)
      || (head && cl->selected()==clen-1 && (*cl)[clen-1]==head);
  if(!canReuse) {
    cl = Clause::fromIterator(Clause::Iterator(*cl), Unit::ASSUMPTION,
	new Inference1(Inference::REORDER_LITERALS, cl));
    cl->setAge(cl0->age());
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

  //add producing rule to a structure
  NOT_IMPLEMENTED;
}

void TabulationAlgorithm::addGoalProducingRule(Clause* oldGoal)
{
  CALL("TabulationAlgorithm::addGoalProducingRule");
  ASS_EQ(oldGoal->selected(), 1);

  if(oldGoal->length()==1) {
    return;
  }

  Literal* activator = (*oldGoal)[0];
  Clause* newGoal = generateGoal(oldGoal, activator);

  //add producing rule to a structure
  NOT_IMPLEMENTED;
}

void TabulationAlgorithm::processGoal(Clause* cl)
{
  CALL("TabulationAlgorithm::processGoal");
  ASS_G(cl->length(),0);

  selectGoalLiteral(cl);
  ASS_EQ(cl->selected(),1);

  addGoalProducingRule(cl);

  Literal* selLit = (*cl)[0];
  if(_glContainer.isSubsumed(selLit)) {
    return;
  }

  _glContainer.add(selLit);

  SLQueryResultIterator qrit = _theoryContainer.getIndex()->getUnifications(selLit, true, true);
  while(qrit.hasNext()) {
    SLQueryResult qres = qrit.next();

    if(qres.clause->length()==1) {
      _unprocLemmaContainer.add(qres.clause);
      continue;
    }
    Clause* newGoal = generateGoal(qres.clause, qres.literal, cl->age());
    addGoal(newGoal);
    addProducingRule(qres.clause, qres.literal);
  }
}


MainLoopResult TabulationAlgorithm::run()
{
  CALL("TabulationAlgorithm::run");

  if(_refutation) {
    return MainLoopResult(Statistics::REFUTATION, _refutation);
  }



  return MainLoopResult(Statistics::UNKNOWN);
}


}

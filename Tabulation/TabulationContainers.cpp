/**
 * @file TabulationContainers.cpp
 * Implements class TabulationContainers.
 */

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/Environment.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"

#include "Indexing/LiteralSubstitutionTree.hpp"

#include "Shell/Options.hpp"

#include "TabulationAlgorithm.hpp"

#include "TabulationContainers.hpp"


namespace Tabulation
{

///////////////////////
// GIContainer
//

GIContainer::GIContainer()
{
  CALL("GIContainer::GIContainer");

  LiteralIndexingStructure* lis = new LiteralSubstitutionTree();
  _unifIndex = new GeneratingLiteralIndex(lis);
  _unifIndex->attachContainer(this);
}

void GIContainer::add(Clause* c)
{
  CALL("GIContainer::add");

  addedEvent.fire(c);
}


/////////////////////////
// GoalLiteralContainer
//

GoalLiteralContainer::GoalLiteralContainer()
{
  CALL("GoalLiteralContainer::GoalLiteralContainer");

  //TODO: check literal code tree implementation and replace SubstitutionTree by CodeTree
  _index = new LiteralSubstitutionTree();
}

void GoalLiteralContainer::add(Literal* lit)
{
  CALL("GoalLiteralContainer::add");
  ASS(!isSubsumed(lit));

  _index->insert(lit, 0);
}

bool GoalLiteralContainer::isSubsumed(Literal* lit)
{
  CALL("GoalLiteralContainer::isSubsumed");

  return _index->getGeneralizations(lit, false, false).hasNext();
}

///////////////////////
// GoalProducer
//

GoalProducer::GoalProducer(TabulationAlgorithm& alg)
: _alg(alg)
{
  CALL("GoalProducer::GoalProducer");

  _lemmaIndex = new LiteralSubstitutionTree();
  _activatorIndex = new LiteralSubstitutionTree();
}

/**
 * Add rule that inserts @c goal among goals of @c _alg when
 * @c onLemma() is called with a literal whose @c acivator is
 * an instance of.
 */
void GoalProducer::addRule(Clause* goal, Literal* activator)
{
  CALL("GoalProducer::addRule");

  if(_lemmaIndex->getGeneralizations(activator, false, false).hasNext()) {
    _alg.addGoal(goal);
    return;
  }

  SLQueryResultIterator qrit = _lemmaIndex->getUnifications(activator, false, true);
  while(qrit.hasNext()) {
    SLQueryResult qr = qrit.next();
    _alg.addGoal(makeInstance(goal, qr.substitution.ref(), false));
  }

  _activatorIndex->insert(activator, goal);
}

Clause* GoalProducer::makeInstance(Clause* cl, ResultSubstitution& subst, bool clIsResult)
{
  CALL("GoalProducer::makeResultInstance");

  static LiteralStack lits;
  lits.reset();

  Clause::Iterator cit(*cl);
  while(cit.hasNext()) {
    Literal* l0 = cit.next();
    Literal* lInst = subst.apply(l0, clIsResult);
    lits.push(lInst);
  }

  Clause* res = Clause::fromStack(lits, cl->inputType(),
      new Inference1(Inference::INSTANCE_GENERATION, cl));
  res->setAge(cl->age());

  res = TabulationAlgorithm::removeDuplicateLiterals(res);

  return res;
}

void GoalProducer::onLemma(Clause* lemma)
{
  CALL("GoalProducer::onLemma");
  ASS_EQ(lemma->length(), 1);

  Literal* lemmaLit = (*lemma)[0];

  typedef pair<Literal*,Clause*> LCPair;
  static Stack<LCPair> toRemove;
  toRemove.reset();

  //First get instances, these can be removed from the set of rules
  {
    SLQueryResultIterator qrit = _activatorIndex->getInstances(lemmaLit, false, false);
    while(qrit.hasNext()) {
      SLQueryResult qr = qrit.next();
      RSTAT_CTR_INC("goal produced (gp rule finished)");
      _alg.addGoal(qr.clause);
      toRemove.push(make_pair(qr.literal, qr.clause));
    }
  }
  while(toRemove.isNonEmpty()) {
    LCPair p = toRemove.pop();
    _activatorIndex->remove(p.first, p.second);
  }


  SLQueryResultIterator qrit = _activatorIndex->getUnifications(lemmaLit, false, true);
  while(qrit.hasNext()) {
    SLQueryResult qr = qrit.next();
    RSTAT_CTR_INC("goal produced (instance of gp rule)");
    Clause* goal = makeInstance(qr.clause, qr.substitution.ref(), true);
    _alg.addGoal(goal);
//    cout<<"l: "<<lemma->toString()<<endl;
//    cout<<"g: "<<goal->toString()<<endl;
  }

  _lemmaIndex->insert(lemmaLit, lemma);
}

}





























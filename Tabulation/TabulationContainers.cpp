/**
 * @file TabulationContainers.cpp
 * Implements class TabulationContainers.
 */

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"

#include "Indexing/LiteralSubstitutionTree.hpp"

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
//// LTContainer
////
//
//LTContainer::LTContainer()
//{
//  CALL("LTContainer::LTContainer");
//
//  _resolution = new BinaryResolution(getIndex());
//}

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

  _index = new LiteralSubstitutionTree();
}

/**
 * Add rule that inserts @c goal among goals of @c _alg when
 * @c onLemma() is called with a literal whose @c acivator is
 * an instance of.
 */
void GoalProducer::addRule(Clause* goal, Literal* activator)
{
  CALL("GoalProducer::addRule");

  _index->insert(activator, goal);
}

Clause* GoalProducer::makeResultInstance(Clause* resCl, ResultSubstitution& subst)
{
  CALL("GoalProducer::makeResultInstance");

  static LiteralStack lits;
  lits.reset();

  Clause::Iterator cit(*resCl);
  while(cit.hasNext()) {
    Literal* l0 = cit.next();
    Literal* lInst = subst.applyToResult(l0);
    lits.push(lInst);
  }

  Clause* res = Clause::fromStack(lits, resCl->inputType(),
      new Inference1(Inference::INSTANCE_GENERATION, resCl));
  res->setAge(resCl->age());
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
    SLQueryResultIterator qrit = _index->getInstances(lemmaLit, false, false);
    while(qrit.hasNext()) {
      SLQueryResult qr = qrit.next();
      _alg.addGoal(qr.clause);
      toRemove.push(make_pair(qr.literal, qr.clause));
    }
  }
  while(toRemove.isNonEmpty()) {
    LCPair p = toRemove.pop();
    _index->remove(p.first, p.second);
  }


  SLQueryResultIterator qrit = _index->getUnifications(lemmaLit, false, true);
  while(qrit.hasNext()) {
    SLQueryResult qr = qrit.next();
    _alg.addGoal(makeResultInstance(qr.clause, qr.substitution.ref()));
  }
}

}





























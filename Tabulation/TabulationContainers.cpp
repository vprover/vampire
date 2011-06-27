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

#undef LOGGING
#define LOGGING 0


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


///////////////////////
// AWClauseContainer
//

AWClauseContainer::AWClauseContainer()
: _ageRatio(1), _weightRatio(1), _balance(0), _size(0)
{
}

bool AWClauseContainer::isEmpty() const
{
  CALL("AWClauseContainer::isEmpty");
//  if(_ageRatio && _weightRatio && _ageQueue.isEmpty()!=_weightQueue.isEmpty())
//  {
//    cout<<" ----  age   ----"<<endl;
//    _ageQueue.output(cout);
//    cout<<" ---- weight ----"<<endl;
//    _weightQueue.output(cout);
//  }

  ASS(!_ageRatio || !_weightRatio || _ageQueue.isEmpty()==_weightQueue.isEmpty());
  return _ageQueue.isEmpty() && _weightQueue.isEmpty();
}


/**
 * Add @b c clause in the queue.
 * @since 31/12/2007 Manchester
 */
void AWClauseContainer::add(Clause* cl)
{
  CALL("AWClauseContainer::add");
  ASS(_ageRatio > 0 || _weightRatio > 0);

  if (_ageRatio) {
    _ageQueue.insert(cl);
  }
  if (_weightRatio) {
    _weightQueue.insert(cl);
  }
  _size++;
  addedEvent.fire(cl);
}

/**
 * Remove Clause from the container.
 */
bool AWClauseContainer::remove(Clause* cl)
{
  CALL("AWClauseContainer::remove");

  bool removed;
  if(_ageRatio) {
    removed = _ageQueue.remove(cl);
    if(_weightRatio) {
      ALWAYS(_weightQueue.remove(cl)==removed);
    }
  }
  else {
    ASS(_weightRatio);
    removed = _weightQueue.remove(cl);
  }

  if(removed) {
    _size--;
    removedEvent.fire(cl);
  }
  return removed;
}


/**
 * Return the next selected clause and remove it from the queue.
 */
Clause* AWClauseContainer::popSelected()
{
  CALL("AWClauseContainer::popSelected");
  ASS( ! isEmpty());

  _size--;

  bool byWeight;
  if (! _ageRatio) {
    byWeight = true;
  }
  else if (! _weightRatio) {
    byWeight = false;
  }
  else if (_balance > 0) {
    byWeight = true;
  }
  else if (_balance < 0) {
    byWeight = false;
  }
  else {
    byWeight = (_ageRatio <= _weightRatio);
  }

  Clause* cl;
  if (byWeight) {
    _balance -= _ageRatio;
    cl = _weightQueue.pop();
    ALWAYS(_ageQueue.remove(cl));
  }
  else {
    _balance += _weightRatio;
    cl = _ageQueue.pop();
    ALWAYS(_weightQueue.remove(cl));
  }
  selectedEvent.fire(cl);
  return cl;
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

  LOG("G added rule "<<activator->toString()<<" --> "<<goal->toString());

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





























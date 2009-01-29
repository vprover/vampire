/**
 * @file Passive.cpp
 * Implements class Passive for the queue of passive clauses.
 * @since 30/12/2007 Manchester
 */

#include "../Lib/Environment.hpp"

#include "../Kernel/Term.hpp"
#include "../Kernel/Clause.hpp"

#include "../Shell/Statistics.hpp"

#include "AWPassiveClauseContainer.hpp"

using namespace Kernel;
using namespace Saturation;

/**
 * Comparison of clauses. The comparison uses four orders in the
 * following order:
 * <ol><li>by weight;</li>
 *     <li>by age;</li>
 *     <li>by input type;</li>
 *     <li>by number.</li>
 * </ol>
 * @since 30/12/2007 Manchester
 */
bool WeightQueue::lessThan(Clause* c1,Clause* c2)
{
  CALL("WeightQueue::lessThan");

  if (c1->weight() < c2->weight()) {
    return true;
  }
  if (c2->weight() < c1->weight()) {
    return false;
  }
  if (c1->age() < c2->age()) {
    return true;
  }
  if (c2->age() < c1->age()) {
    return false;
  }
  if (c1->inputType() < c2->inputType()) {
    return false;
  }
  if (c2->inputType() < c1->inputType()) {
    return true;
  }
  return c1->number() < c2->number();
} // WeightQueue::lessThan


/**
 * Comparison of clauses. The comparison uses four orders in the
 * following order:
 * <ol><li>by age;</li>
 *     <li>by weight;</li>
 *     <li>by input type;</li>
 *     <li>by number.</li>
 * </ol>
 * @since 30/12/2007 Manchester
 */
bool AgeQueue::lessThan(Clause* c1,Clause* c2)
{
  CALL("AgeQueue::lessThan");

  if (c1->age() < c2->age()) {
    return true;
  }
  if (c2->age() < c1->age()) {
    return false;
  }
  if (c1->weight() < c2->weight()) {
    return true;
  }
  if (c2->weight() < c1->weight()) {
    return false;
  }
  if (c1->inputType() < c2->inputType()) {
    return false;
  }
  if (c2->inputType() < c1->inputType()) {
    return true;
  }
  return c1->number() < c2->number();
} // WeightQueue::lessThan


AWPassiveClauseContainer::~AWPassiveClauseContainer()
{
  ClauseQueue::Iterator cit(_ageQueue);
  while(cit.hasNext()) {
    Clause* cl=cit.next();
    cl->setStore(Clause::NONE);
  }
}

/**
 * Add @b c clause in the queue.
 * @since 31/12/2007 Manchester
 */
void AWPassiveClauseContainer::add(Clause* c)
{
  CALL("AWPassiveClauseContainer::add");
  ASS(_ageRatio > 0 || _weightRatio > 0);

  if (_ageRatio) {
    _ageQueue.insert(c);
  }
  if (_weightRatio) {
    _weightQueue.insert(c);
  }
  c->setStore(Clause::PASSIVE);
  env.statistics->passiveClauses++;
  addedEvent.fire(c);
} // AWPassiveClauseContainer::add

/**
 * Return the next selected clause and remove it from the queue.
 * @since 31/12/2007 Manchester
 */
Clause* AWPassiveClauseContainer::popSelected()
{
  CALL("AWPassiveClauseContainer::popSelected");
  ASS( ! isEmpty());

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

  if (byWeight) {
    _balance -= _ageRatio;
    Clause* c = _weightQueue.pop();
    _ageQueue.remove(c);
    return c;
  }
  _balance += _weightRatio;
  Clause* c = _ageQueue.pop();
  _weightQueue.remove(c);
  removedEvent.fire(c);
  return c;
} // AWPassiveClauseContainer::popSelected


/**
 * @file ClauseContainer.cpp
 * Implementing ClauseContainer and its descendants.
 */

#include "../Kernel/Clause.hpp"

#include "ClauseContainer.hpp"

using namespace Saturation;

void ClauseContainer::addClauses(ClauseIterator cit)
{
  while(cit.hasNext()) {
    add(cit.next());
  }
}

void RandomAccessClauseContainer::removeClauses(ClauseIterator cit)
{
  while(cit.hasNext()) {
    remove(cit.next());
  }
}

void UnprocessedClauseContainer::add(Clause* c)
{
  _data.push(c);
  c->setStore(Clause::UNPROCESSED);
  addedEvent.fire(c);
}

Clause* UnprocessedClauseContainer::pop()
{
  Clause* res=_data.pop();
  removedEvent.fire(res);
  return res;
}

void ActiveClauseContainer::add(Clause* c)
{
  c->setStore(Clause::ACTIVE);
  addedEvent.fire(c);
}

void ActiveClauseContainer::remove(Clause* c)
{
  removedEvent.fire(c);
}

/**
 * @file ClauseContainer.cpp
 * Implementing ClauseContainer and its descendants.
 */

#include "../Lib/Environment.hpp"

#include "../Kernel/Clause.hpp"

#include "../Shell/Statistics.hpp"

#include "ClauseContainer.hpp"

using namespace Kernel;
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

UnprocessedClauseContainer::~UnprocessedClauseContainer()
{
  while(!_data.isEmpty()) {
    Clause* cl=_data.pop();
    cl->setStore(Clause::NONE);
  }
}

void UnprocessedClauseContainer::add(Clause* c)
{
  _data.push(c);
  c->setStore(Clause::UNPROCESSED);
  env.statistics->generatedClauses++;
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
  env.statistics->activeClauses++;
  addedEvent.fire(c);
}

void ActiveClauseContainer::remove(Clause* c)
{
  removedEvent.fire(c);
}

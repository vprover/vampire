/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file Indexing/Index.cpp
 * Implements class Index.
 *
 */

#include "Index.hpp"
#include "Forwards.hpp"

namespace Indexing
{

using namespace Lib;
using namespace Kernel;
using namespace Saturation;

Index::~Index()
{
  if(!_addedSD.isEmpty()) {
    ASS(!_removedSD.isEmpty());
    _addedSD->unsubscribe();
    _removedSD->unsubscribe();
  }
}

/**
 * Attaches index to a clause container
 *
 * Can only be called once per @b Index object lifetime.
 */
void Index::attachContainer(ClauseContainer* cc)
{
  ASS(_addedSD.isEmpty()); //only one container can be attached

  _addedSD = cc->addedEvent.subscribe(this,&Index::onAddedToContainer);
  _removedSD = cc->removedEvent.subscribe(this,&Index::onRemovedFromContainer);
}

void GoalDirectedPredicateIndex::handleClause(Clause* c, bool adding)
{
  for (const auto& lit : iterTraits(goal ? c->getSelectedLiteralIterator() : c->iterLits())) {
    if (lit->isEquality()) {
      continue;
    }
    if (goal) {
      if (lit->isPositive()) {
        continue;
      }
    } else {
      if (lit->isNegative()) {
        continue;
      }
    }
    DHSet<Clause*>* ptr;
    _container.getValuePtr(lit->functor(), ptr);
    if (adding) {
      ptr->insert(c);
    } else {
      ASS(ptr);
      ptr->remove(c);
    }
  }
}

ClauseIterator GoalDirectedPredicateIndex::get(Literal* lit)
{
  ASS(!lit->isEquality());
  if (goal) {
    ASS(lit->isPositive());
  } else {
    ASS(lit->isNegative());
  }
  auto ptr = _container.find(lit->functor());
  if (!ptr) {
    return ClauseIterator::getEmpty();
  }
  return ptr->iterator();
}

}

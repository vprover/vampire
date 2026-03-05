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
 * @file ClauseQueue.cpp
 * Implements class ClauseQueue of clause priority queues
 * @since 30/12/2007 Manchester
 */

#include "Clause.hpp"
#include "ClauseQueue.hpp"

using namespace std;
using namespace Kernel;

ClauseQueue::ClauseQueue()
    : _set(Comparator{this})
{
}

ClauseQueue::~ClauseQueue()
{
}

void ClauseQueue::insert(Clause* c)
{
  _set.insert(c);
}

bool ClauseQueue::remove(Clause* c)
{
  return _set.erase(c) > 0;
}

Clause* ClauseQueue::pop()
{
  ASS(!_set.empty());

  auto it = _set.begin();
  Clause* c = *it;
  _set.erase(it);
  return c;
}

void ClauseQueue::removeAll()
{
  _set.clear();
}

void ClauseQueue::output(std::ostream& str) const
{
  for (Clause* c : _set) {
    str << c->toString() << '\n';
  }
}

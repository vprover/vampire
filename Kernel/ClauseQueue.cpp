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

ClauseQueue::ClauseQueue(const Shell::Options& opt)
    : _opt(opt), _set(Comparator{this})
{
}

ClauseQueue::~ClauseQueue()
{
}

ClauseInfo ClauseQueue::makeInfo(Clause* c) const
{
  return {c, c->age(), c->weightForClauseSelection(_opt), c->inputType(), c->number()};
}

void ClauseQueue::insert(Clause* c)
{
  _set.insert(makeInfo(c));
}

bool ClauseQueue::remove(Clause* c)
{
  auto it = _set.find(makeInfo(c));
  if (it != _set.end()) {
    _set.erase(it);
    return true;
  }
  return false;
}

Clause* ClauseQueue::pop()
{
  ASS(!_set.empty());

  auto it = _set.begin();
  Clause* c = it->clause;
  _set.erase(it);
  return c;
}

void ClauseQueue::removeAll()
{
  _set.clear();
}

void ClauseQueue::output(std::ostream& str) const
{
  for (const auto& info : _set) {
    str << info.clause->toString() << '\n';
  }
}

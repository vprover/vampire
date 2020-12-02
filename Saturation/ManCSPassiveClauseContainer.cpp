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
 * @file ManCSPassiveClauseContainer.cpp
 * Defines the class ManCSPassiveClauseContainer
 */
#include <iostream>
#include <algorithm>
#include "ManCSPassiveClauseContainer.hpp"
#include "Lib/VirtualIterator.hpp"

namespace Saturation
{
using namespace Lib;
using namespace Kernel;

/*
 * this class wraps the iterator of std::vector into IteratorCore required by Vampire.
 */
class VectorIteratorWrapper : public IteratorCore<Clause*>
{
public:
  CLASS_NAME(VectorIteratorWrapper);
  USE_ALLOCATOR(VectorIteratorWrapper);
  
  explicit VectorIteratorWrapper(const std::vector<Clause*>& v) : curr(v.begin()), end(v.end()) {}
  bool hasNext() { return curr != end; };
  Clause* next() { auto cl = *curr; curr = std::next(curr); return cl;};

private:
  std::vector<Clause*>::const_iterator curr;
  const std::vector<Clause*>::const_iterator end;
};

void ManCSPassiveClauseContainer::add(Clause* cl)
{
  CALL("ManCSPassiveClauseContainer::add");
  clauses.push_back(cl);
  addedEvent.fire(cl);
}

void ManCSPassiveClauseContainer::remove(Clause* cl)
{
  CALL("ManCSPassiveClauseContainer::remove");
  ASS(cl->store()==Clause::PASSIVE);

  auto it = std::find(clauses.begin(),clauses.end(),cl);
  ASS(it != clauses.end());
  clauses.erase(it);

  removedEvent.fire(cl);
  ASS(cl->store()!=Clause::PASSIVE);
}

Clause* ManCSPassiveClauseContainer::popSelected()
{
  CALL("ManCSPassiveClauseContainer::popSelected");
  ASS(!clauses.empty());

  std::vector<Clause*>::iterator selectedClauseIt;
  while(true)
  {
    // ask user to pick a clause id
    std::cout << "Pick a clause:\n";
    std::string id;
    std::cin >> id;
    unsigned selectedId = std::stoi(id);

    // search clause with that id
    selectedClauseIt = std::find_if(clauses.begin(), clauses.end(), 
      [&](Clause* c) -> bool { return c->number() == selectedId; });
    if(selectedClauseIt != clauses.end())
    {
      break;
    }
    else
    {
      std::cout << "User error: No clause in Passive has id " << id << "!\n";
    }
  }

  auto selectedClause	= *selectedClauseIt;
  clauses.erase(selectedClauseIt);
  selectedEvent.fire(selectedClause);

  return selectedClause;
}

unsigned ManCSPassiveClauseContainer::sizeEstimate() const { return clauses.size(); }
bool ManCSPassiveClauseContainer::isEmpty() const { return clauses.empty(); }
}

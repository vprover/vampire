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
 * Can only be called once per @b Index obejct lifetime.
 */
void Index::attachContainer(ClauseContainer* cc)
{
  ASS(_addedSD.isEmpty()); //only one container can be attached

  _addedSD = cc->addedEvent.subscribe(this,&Index::onAddedToContainer);
  _removedSD = cc->removedEvent.subscribe(this,&Index::onRemovedFromContainer);
}


std::ostream& operator<<(std::ostream& out, TermQueryResult const& self)
{ 
  out << "TermQueryResult("
      <<   "term: "         << self.term
      << ", literal: "      << *self.literal
      << ", clause: "       << *self.clause
      << ", substitution: " << self.substitution
      << ", constraints: " ;

  auto toTerm = [&](pair<TermList, int> const& x) 
                { return self.substitution->apply(x.first, x.second); };
  auto writeConst = [&](UnificationConstraint const&c)
                    { out << toTerm(c.first) << " = " << toTerm(c.second); };

  out << "[";
  auto iter = self.constraints->iterFifo();
  if (iter.hasNext()) {
    writeConst(iter.next());
    while (iter.hasNext()) {
      out << ", ";
      writeConst(iter.next());
    }
  }
  out << "]";
  out << ")"; 
  return out;
}

}

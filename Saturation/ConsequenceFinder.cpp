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
 * @file ConsequenceFinder.cpp
 * Implements class ConsequenceFinder.
 */

#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/SharedSet.hpp"
#include "Debug/TimeProfiling.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Signature.hpp"

#include "Shell/Options.hpp"

#include "ConsequenceFinder.hpp"
#include "SaturationAlgorithm.hpp"

namespace Saturation
{

using namespace std;
using namespace Lib;
using namespace Kernel;

void ConsequenceFinder::init(SaturationAlgorithm* sa)
{
  _sa=sa;

  ClauseContainer* cc=_sa->getSimplifyingClauseContainer();
  _sdInsertion = cc->addedEvent.subscribe(this,&ConsequenceFinder::onClauseInserted);
  _sdRemoval = cc->removedEvent.subscribe(this,&ConsequenceFinder::onClauseRemoved);
}

ConsequenceFinder::~ConsequenceFinder()
{
  _sdInsertion->unsubscribe();
  _sdRemoval->unsubscribe();
}

void ConsequenceFinder::onNewPropositionalClause(Clause* cl)
{
  TIME_TRACE(TimeTrace::CONSEQUENCE_FINDING);

  //remove duplicate literals (necessary for tautology deletion)
  Clause* dlrCl=_dlr.simplify(cl);

  bool dlrSimplified=dlrCl!=cl;
  if(dlrSimplified) {
    //the function will be called again with the clause that is already simplified
    //TODO: get some cheaper way of testing for duplicate literals presence
    dlrCl->destroyIfUnnecessary();
    return;
  }


  if(!cl->noSplits() || !_td.simplify(cl)) {
    return;
  }
  Literal* pos=0;
  bool horn=true;
  for (auto l : cl->iterLits()) {
    if(!env.signature->getPredicate(l->functor())->label()) {
      return;
    }
    if(l->isPositive()) {
      if(pos) {
        horn=false;
      }
      else {
        pos=l;
      }
    }
  }

  std::cout << "Pure cf clause: " << cl->toNiceString() <<endl;

  if(!horn || !pos) {
    return;
  }

  unsigned red=pos->functor(); //redundant cf symbol number
  if(_redundant[red]) {
    return;
  }
  _redundant[red]=true;

  //we will remove the redundant clauses later -- now we may be at some unsuitable part
  //of the saturation algorithm loop
  _redundantsToHandle.push(red);

  std::cout << "Consequence found: " << env.signature->predicateName(red) << endl;
}

void ConsequenceFinder::onAllProcessed()
{
  TIME_TRACE(TimeTrace::CONSEQUENCE_FINDING);

  while(_redundantsToHandle.isNonEmpty()) {
    unsigned red=_redundantsToHandle.pop();

    ClauseSL* rlist=_index[red];
    if(rlist) {
      _index[red]=0;
      while(rlist->isNonEmpty()) {
        Clause* rcl=rlist->pop();
        // Martin: there was comma in an if-statement -- Highly suspicious!
        // This has the same effect and doesn't trigger a warning, but should be revised when this code is understood.
        (void)(rcl->store()!=Clause::UNPROCESSED && rcl->store()!=Clause::NONE);
        if(rcl->store()) {
          //this case is not very likely to happen, but possible -- one clause is redundant
          //both due to the consequence-finding mode and to some backward simplification
          continue;
        }
        _sa->removeActiveOrPassiveClause(rcl);
      }
      delete rlist;
    }
  }
}

/**
 * Return true if a clause is redundant for the process of
 * consequence finding and can therefore be deleted
 */
bool ConsequenceFinder::isRedundant(Clause* cl)
{
  for (auto l : cl->iterLits()) {
    unsigned fn = l->functor();
    if(!env.signature->getPredicate(fn)->label()) {
      continue;
    }
    if(_redundant[fn]) {
      return true;
    }
  }
  return false;
}


void ConsequenceFinder::onClauseInserted(Clause* cl)
{
  TIME_TRACE(TimeTrace::CONSEQUENCE_FINDING);

  bool red=false;
  for (auto l : cl->iterLits()) {
    unsigned fn = l->functor();
    if(!env.signature->getPredicate(fn)->label()) {
      continue;
    }
    if(_redundant[fn]) {
      red=true;
    }
    else {
      indexClause(fn, cl, true);
    }
  }
  if(red) {
    //the clause is already redundant, so we should delete it

    //it may not be the right moment to call this function, so in
    //case of problems just comment this out (it will lead just to
    //some extra work of the algorithm).
    //_sa->removeActiveOrPassiveClause(cl);
  }

}

void ConsequenceFinder::onClauseRemoved(Clause* cl)
{
  TIME_TRACE(TimeTrace::CONSEQUENCE_FINDING);

  for (auto l : cl->iterLits()) {
    unsigned fn = l->functor();
    if(!env.signature->getPredicate(fn)->label()) {
      continue;
    }
    if(!_redundant[fn]) {
      indexClause(fn, cl, false);
    }
  }
}

/**
 * Perform index maintenance (either add or remove a clause from index
 * for the predicate @b indexNum)
 */
void ConsequenceFinder::indexClause(unsigned indexNum, Clause* cl, bool add)
{
  if(add) {
    if(!_index[indexNum]) {
      _index[indexNum]=new ClauseSL();
    }
    _index[indexNum]->insert(cl);
  }
  else {
    ASS(_index[indexNum]);
    _index[indexNum]->remove(cl);
  }
}


}

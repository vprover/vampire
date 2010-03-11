/**
 * @file ConsequenceFinder.cpp
 * Implements class ConsequenceFinder.
 */

#include "../Lib/Environment.hpp"
#include "../Lib/Metaiterators.hpp"
#include "../Lib/SharedSet.hpp"
#include "../Lib/SkipList.hpp"

#include "../Kernel/BDD.hpp"
#include "../Kernel/Clause.hpp"
#include "../Kernel/Signature.hpp"

#include "../Shell/Options.hpp"

#include "ConsequenceFinder.hpp"
#include "SaturationAlgorithm.hpp"

namespace Saturation
{

using namespace Lib;
using namespace Kernel;

void ConsequenceFinder::init(SaturationAlgorithm* sa)
{
  CALL("ConsequenceFinder::init");

  _sa=sa;

  ClauseContainer* cc=_sa->getSimplificationClauseContainer();
  _sdInsertion = cc->addedEvent.subscribe(this,&ConsequenceFinder::onClauseInserted);
  _sdRemoval = cc->removedEvent.subscribe(this,&ConsequenceFinder::onClauseRemoved);
}

ConsequenceFinder::~ConsequenceFinder()
{
  CALL("ConsequenceFinder::~ConsequenceFinder");

  _sdInsertion->unsubscribe();
  _sdRemoval->unsubscribe();
}


void ConsequenceFinder::onNewPropositionalClause(Clause* cl)
{
  CALL("ConsequenceFinder::onNewPropositionalClause");

  if(!cl->noSplits() || !BDD::instance()->isFalse(cl->prop()) || !_td.simplify(cl)) {
    return;
  }
  Literal* pos=0;
  bool horn=true;
  Clause::Iterator it(*cl);
  while(it.hasNext()) {
    Literal* l=it.next();
    if(!env.signature->getPredicate(l->functor())->cfName()) {
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

  env.out << "Pure cf clause: " << cl->toNiceString() <<endl;

  if(!horn || !pos) {
    return;
  }

  unsigned red=pos->functor(); //redundant cf symbol number
  _redundant[red]=true;

  env.out << "Consequence found: " << env.signature->predicateName(red) << endl;

  ClauseSL* rlist=_index[red];
  if(rlist) {
    _index[red]=0;
    while(rlist->isNonEmpty()) {
      Clause* rcl=rlist->pop();
      _sa->removeActiveOrPassiveClause(rcl);
    }
    delete rlist;
  }
}

/**
 * Return true if a clause is redundant for the process of
 * consequence finding and can therefore be deleted
 */
bool ConsequenceFinder::isRedundant(Clause* cl)
{
  CALL("ConsequenceFinder::isRedundant");

  Clause::Iterator it(*cl);
  while(it.hasNext()) {
    unsigned fn=it.next()->functor();
    if(!env.signature->getPredicate(fn)->cfName()) {
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
  CALL("ConsequenceFinder::onClauseInserted");

  bool red=false;
  Clause::Iterator it(*cl);
  while(it.hasNext()) {
    unsigned fn=it.next()->functor();
    if(!env.signature->getPredicate(fn)->cfName()) {
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
  CALL("ConsequenceFinder::onClauseRemoved");

  Clause::Iterator it(*cl);
  while(it.hasNext()) {
    unsigned fn=it.next()->functor();
    if(!env.signature->getPredicate(fn)->cfName()) {
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
  CALL("ConsequenceFinder::indexClause");

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

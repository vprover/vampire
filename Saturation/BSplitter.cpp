/**
 * @file BSplitter.cpp
 * Implements class BSplitter.
 */

#include "../Lib/SharedSet.hpp"

#include "../Kernel/Clause.hpp"
#include "../Kernel/Inference.hpp"

#include "BSplitter.hpp"

namespace Saturation
{

void BSplitter::init(SaturationAlgorithm* sa)
{
  CALL("BSplitter::init");

  _nextLev=1;
  _sa=sa;
}

bool BSplitter::split(Clause* cl)
{
  CALL("BSplitter::split");

  Clause* c1;
  Clause* c2;
  if(!getComponents(cl,c1,c2)) {
    return false;
  }

  NOT_IMPLEMENTED;
}

void BSplitter::onClauseReduction(Clause* cl, Clause* to, Clause* premise, bool forward)
{
  CALL("BSplitter::onClauseReduction");

  NOT_IMPLEMENTED;
}

void BSplitter::onNewClause(Clause* cl)
{
  CALL("BSplitter::onNewClause");

  NOT_IMPLEMENTED;
}

bool BSplitter::getComponents(Clause* icl, Clause*& ocl1, Clause*& ocl2)
{
  CALL("BSplitter::getComponents");

  NOT_IMPLEMENTED;
}

/**
 * Return a split set of a new clause
 *
 * Assumes that clauses referred to by cl->inference() object
 * are actual premisses of @b cl.
 */
SplitSet* BSplitter::getNewClauseSplitSet(Clause* cl)
{
  CALL("BSplitter::getNewClauseSplitSet");

  SplitSet* res;
  Inference* inf=cl->inference();
  Inference::Iterator it=inf->iterator();

  if(stackSplitting()) {
    res=SplitSet::getEmpty();

    while(inf->hasNext(it)) {
      Clause* prem=static_cast<Clause*>(inf->next(it));
      ASS(prem->isClause());

      res=res->getUnion(prem->splits());
    }
  }
  else {
    SplitLevel maxLev=0;

    while(inf->hasNext(it)) {
      Clause* prem=static_cast<Clause*>(inf->next(it));
      ASS(prem->isClause());

      if(!prem->splits()->isEmpty()) {
	maxLev=max(maxLev,prem->splits()->sval());
      }
    }

    if(maxLev) {
      res=SplitSet::getSingleton(maxLev);
    }
    else {
      res=SplitSet::getEmpty();
    }
  }
  return res;
}


void BSplitter::backtrack(Clause* cl)
{
  CALL("BSplitter::backtrack");

  NOT_IMPLEMENTED;
}


}

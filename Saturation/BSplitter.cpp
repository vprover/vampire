/**
 * @file BSplitter.cpp
 * Implements class BSplitter.
 */

#include "../Lib/DHSet.hpp"
#include "../Lib/SharedSet.hpp"

#include "../Kernel/Clause.hpp"
#include "../Kernel/Inference.hpp"

#include "BSplitter.hpp"
#include "SaturationAlgorithm.hpp"

namespace Saturation
{

using namespace Lib;
using namespace Kernel;

void BSplitter::init(SaturationAlgorithm* sa)
{
  CALL("BSplitter::init");

  _nextLev=1;
  _sa=sa;
}

bool BSplitter::split(Clause* cl)
{
  CALL("BSplitter::split");

  Clause* comp;
  comp=getComponent(cl);
  if(!comp) {
    return false;
  }

  SplitLevel lev=_nextLev++;
  SplitRecord* sr=new SplitRecord(lev, cl, comp);

  //update "dependent" field of base SplitRecords
  SplitSet::Iterator bsit(cl->splits());
  while(bsit.hasNext()) {
    SplitLevel blev=bsit.next();
    _db[blev]->dependent.push(lev);
  }

  ASS(!_db[lev]);
  _db[lev]=sr;

  assignClauseSplitSet(comp, cl->splits()->getUnion(SplitSet::getSingleton(lev)));
  _sa->addNewClause(comp);

  return true;
}

void BSplitter::onClauseReduction(Clause* cl, Clause* to, Clause* premise, bool forward)
{
  CALL("BSplitter::onClauseReduction");

  NOT_IMPLEMENTED;
}

void BSplitter::onNewClause(Clause* cl)
{
  CALL("BSplitter::onNewClause");

  if(!cl->splits()) {
    SplitSet* splits=getNewClauseSplitSet(cl);
    assignClauseSplitSet(cl, splits);
  }

  NOT_IMPLEMENTED;
}

/**
 * Return the component that should be refuted if the clause @b icl
 * should be splitted or 0 otherwise
 *
 * The other component is not explicitly returned. Its literals are
 * those of @b icl that are not present in the result clause. It is
 * done this way so that the other component can be built after we
 * obtain the empty clause refuting the first component.
 */
Clause* BSplitter::getComponent(Clause* icl)
{
  CALL("BSplitter::getComponent");

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

void BSplitter::assignClauseSplitSet(Clause* cl, SplitSet* splits)
{
  CALL("BSplitter::assignClauseSplitSet");
  ASS(!cl->splits());

  cl->setSplits(splits);

  //update "children" field of relevant SplitRecords
  SplitSet::Iterator bsit(splits);
  while(bsit.hasNext()) {
    SplitLevel slev=bsit.next();
    _db[slev]->children.push(cl);
  }
}

/**
 * Perform backtracking allowed for by empty clauses in @b emptyClauses
 *
 * Can be called only when there are no unprocessed clauses left.
 * This is to allow for easy clause removal from the saturation algorithm.
 */
void BSplitter::backtrack(ClauseIterator emptyClauses)
{
  CALL("BSplitter::backtrack(ClauseIterator)");
  ASS(emptyClauses.hasNext());
  ASS(_sa->clausesFlushed());

  static ClauseStack toDo;
  toDo.reset();
  toDo.loadFromIterator(emptyClauses);

start:
  Clause* cl=toDo.pop();
  ASS(cl->isEmpty());

  SplitSet* refSplits=cl->splits();
  ASS_G(refSplits->size(),0);

  SplitLevel refLvl=refSplits->maxval(); //refuted level

  //TODO: add alternatives!!!
  NOT_IMPLEMENTED;

  SplitSet* backtracked=getTransitivelyDependentLevels(refLvl);

  ClauseStack::Iterator tdit(toDo);
  while(tdit.hasNext()) {
    Clause* ecl=tdit.next();
    if(ecl->splits()->hasIntersection(backtracked)) {
      tdit.del();
      //TODO: here the empty clause probably can be also deleted from memory
    }
  }

  static ClauseStack trashed;
  static ClauseStack restored;
  ASS(trashed.isEmpty());
  ASS(restored.isEmpty());
  Clause::requestAux();

  SplitSet::Iterator blit(backtracked);
  while(blit.hasNext()) {
    SplitLevel bl=blit.next();
    SplitRecord* sr=_db[bl];

    while(sr->children.isNonEmpty()) {
      Clause* ccl=sr->children.pop();
      if(ccl->hasAux()) {
	continue;
      }
      ASS(ccl->splits()->member(bl));
      trashed.push(ccl);
      ccl->setAux(0);
    }
  }

  SplitSet::Iterator blit2(backtracked);
  while(blit2.hasNext()) {
    SplitLevel bl=blit2.next();
    SplitRecord* sr=_db[bl];

    while(sr->reduced.isNonEmpty()) {
      Clause* rcl=sr->reduced.pop();
      if(rcl->hasAux()) {
	continue;
      }
      ASS(!rcl->splits()->hasIntersection(backtracked));
      restored.push(rcl);
      rcl->setAux(0);
    }

    _db[bl]=0;
    delete sr;
  }

  while(trashed.isNonEmpty()) {
    _sa->removeActiveOrPassiveClause(trashed.pop());
  }

  while(restored.isNonEmpty()) {
    _sa->addNewClause(restored.pop());
  }

  Clause::releaseAux();


  if(toDo.isNonEmpty()) {
    goto start;
  }
}

/**
 * Return set of levels that depend on the splitting level @b lev in
 * a reflexive-transitive closure of the level dependency relation
 */
SplitSet* BSplitter::getTransitivelyDependentLevels(SplitLevel lev)
{
  CALL("BSplitter::getTransitivelyDependentLevels");

  static DHSet<SplitLevel> depSet;
  static LevelStack depStack;
  static LevelStack toDo;
  depSet.reset();
  depStack.reset();
  toDo.reset();

  toDo.push(lev);
  depSet.insert(lev);
  depStack.push(lev);

  while(toDo.isNonEmpty()) {
    SplitLevel l=toDo.pop();
    LevelStack::Iterator dit(_db[l]->dependent);
    while(dit.hasNext()) {
      SplitLevel dl=dit.next();
      if(!depSet.find(dl)) {
	toDo.push(dl);
	depSet.insert(dl);
	depStack.push(dl);
      }
    }
  }
  return SplitSet::getFromArray(depStack.begin(), depStack.size());
}

}

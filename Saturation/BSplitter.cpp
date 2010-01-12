/**
 * @file BSplitter.cpp
 * Implements class BSplitter.
 */

#include "../Lib/DHSet.hpp"
#include "../Lib/IntUnionFind.hpp"
#include "../Lib/Metaiterators.hpp"
#include "../Lib/SharedSet.hpp"

#include "../Kernel/BDD.hpp"
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


/**
 * Register the reduction of the @b cl clause
 *
 * The @b onNewClause method still has to be called for the @b to clause if there is any.
 */
void BSplitter::onClauseReduction(Clause* cl, Clause* premise)
{
  CALL("BSplitter::onClauseReduction");

  if(!premise) {
    return;
  }

  SplitSet* diff=premise->splits()->subtract(cl->splits());

  if(diff->isEmpty()) {
    return;
  }

  SplitSet::Iterator dit(diff);
  while(dit.hasNext()) {
    SplitLevel slev=dit.next();
    cl->incRefCnt();
    _db[slev]->reduced.push(cl);
  }
}

void BSplitter::onNewClause(Clause* cl)
{
  CALL("BSplitter::onNewClause");

  if(!cl->splits()) {
    SplitSet* splits=getNewClauseSplitSet(cl);
    assignClauseSplitSet(cl, splits);
  }
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
Clause* BSplitter::getComponent(Clause* cl)
{
  CALL("BSplitter::getComponent");

  unsigned clen=cl->length();
  if(clen<=1) {
    return 0;
  }

  unsigned posLits=0;

  //Master literal of an variable is the literal
  //with lowest index, in which it appears.
  static DHMap<unsigned, unsigned, IdentityHash> varMasters;
  varMasters.reset();
  IntUnionFind components(clen);

  //TODO:Should we avoid colored literals to be in the splitted-out component?

  for(unsigned i=0;i<clen;i++) {
    Literal* lit=(*cl)[i];
    if(lit->isPositive()) {
      posLits++;
    }
    Term::VariableIterator vit(lit);
    while(vit.hasNext()) {
      unsigned master=varMasters.findOrInsert(vit.next().var(), i);
      if(master!=i) {
	components.doUnion(master, i);
      }
    }
  }
  components.finish();

  int compCnt=components.getComponentCount();

  if(compCnt==1 || (splittingForHorn() && posLits<=1)) {
    return 0;
  }

  static Stack<Literal*> lits;

compAssemblyStart:
  lits.reset();

  IntUnionFind::ComponentIterator cit(components);
  ALWAYS(cit.hasNext());
  IntUnionFind::ElementIterator elit=cit.next();

  unsigned compPosLits=0;
  while(elit.hasNext()) {
    int litIndex=elit.next();
    Literal* lit=(*cl)[litIndex];
    lits.push(lit);
    if(lit->isPositive()) {
      compPosLits++;
    }
  }
  if(splittingForHorn()) {
    if(compPosLits==posLits) {
      return 0;
    }
    if(compPosLits==0) {
      if(cit.hasNext()) {
	goto compAssemblyStart;
      }
      else {
	return 0;
      }
    }
  }

  Clause* res=Clause::fromStack(lits, cl->inputType(), new Inference(Inference::SPLITTING_COMPONENT));
  res->setProp(BDD::instance()->getFalse());
  return res;
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

  if(!stackSplitting()) {
    res=SplitSet::getEmpty();

    while(inf->hasNext(it)) {
      Unit* premu=inf->next(it);
      if(!premu->isClause()) {
	//the premise comes from preprocessing
	continue;
      }
      Clause* prem=static_cast<Clause*>(premu);
      if(!prem->splits()) {
	//the premise comes from preprocessing
	continue;
      }

      res=res->getUnion(prem->splits());
    }
  }
  else {
    SplitLevel maxLev=0;

    while(inf->hasNext(it)) {
      Unit* premu=inf->next(it);
      if(!premu->isClause()) {
	//the premise comes from preprocessing
	continue;
      }
      Clause* prem=static_cast<Clause*>(premu);
      if(!prem->splits()) {
	//the premise comes from preprocessing
	continue;
      }

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
    cl->incRefCnt();
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

  SplitSet* backtracked;
  if(stackSplitting()) {
    backtracked=SplitSet::getRange(refLvl,_nextLev);
  }
  else {
    backtracked=getTransitivelyDependentLevels(refLvl);
  }


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

  //add the other component of the splitted clause (plus possibly some other clauses)
  getAlternativeClauses(_db[refLvl]->base, _db[refLvl]->component, cl, restored);


  SplitSet::Iterator blit(backtracked);
  while(blit.hasNext()) {
    SplitLevel bl=blit.next();
    SplitRecord* sr=_db[bl];

    while(sr->children.isNonEmpty()) {
      Clause* ccl=sr->children.pop();
      if(!ccl->hasAux()) {
	ASS(ccl->splits()->member(bl));
	if(ccl->store()!=Clause::NONE) {
	  trashed.push(ccl);
	}
	ccl->setAux(0);
      }
      ccl->decRefCnt();
    }
  }

  SplitSet::Iterator blit2(backtracked);
  while(blit2.hasNext()) {
    SplitLevel bl=blit2.next();
    SplitRecord* sr=_db[bl];

    while(sr->reduced.isNonEmpty()) {
      Clause* rcl=sr->reduced.pop();
      if(!rcl->hasAux()) {
	ASS(!rcl->splits()->hasIntersection(backtracked));
	restored.push(rcl);
	rcl->setAux(0);
      }
      rcl->decRefCnt();
    }

    _db[bl]=0;
    delete sr;
  }

  while(trashed.isNonEmpty()) {
    Clause* tcl=trashed.pop();
    _sa->removeActiveOrPassiveClause(tcl);
  }

  while(restored.isNonEmpty()) {
    Clause* rcl=restored.pop();
    ASS_EQ(rcl->store(), Clause::NONE);
    _sa->addNewClause(rcl);
  }

  Clause::releaseAux();


  if(toDo.isNonEmpty()) {
    goto start;
  }
}

void BSplitter::getAlternativeClauses(Clause* base, Clause* firstComp, Clause* refutation, ClauseStack& acc)
{
  CALL("BSplitter::getAlternativeClauses");

  Unit::InputType inp=max(base->inputType(), refutation->inputType());

  static DHSet<Literal*> firstLits;
  static Stack<Literal*> secLits;
  firstLits.reset();
  secLits.reset();

  firstLits.loadFromIterator(Clause::Iterator(*firstComp));
  Clause::Iterator bit(*base);
  while(bit.hasNext()) {
    Literal* l=bit.next();
    if(!firstLits.find(l)) {
      secLits.push(l);
    }
  }
  Inference* sinf=new Inference2(Inference::SPLITTING, base, refutation);
  Clause* scl=Clause::fromStack(secLits, inp, sinf);
  scl->setProp(base->prop());
  scl->setSplits(base->splits());
  acc.push(scl);

  if(firstComp->isGround()) {
    //if the first component is ground, add its negation
    Clause::Iterator fcit(*firstComp);
    while(fcit.hasNext()) {
      Literal* glit=fcit.next();
      Inference* ginf=new Inference2(Inference::SPLITTING, base, refutation);
      Clause* gcl=Clause::fromIterator(getSingletonIterator(Literal::oppositeLiteral(glit)), inp, ginf);
      gcl->setProp(base->prop());
      gcl->setSplits(base->splits());
      acc.push(gcl);
    }
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

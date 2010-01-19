/**
 * @file BSplitter.cpp
 * Implements class BSplitter.
 */

#include "../Lib/DHSet.hpp"
#include "../Lib/Environment.hpp"
#include "../Lib/IntUnionFind.hpp"
#include "../Lib/Metaiterators.hpp"
#include "../Lib/SharedSet.hpp"

#include "../Kernel/BDD.hpp"
#include "../Kernel/Clause.hpp"
#include "../Kernel/Inference.hpp"

#include "../Shell/Statistics.hpp"

#include "BSplitter.hpp"
#include "SaturationAlgorithm.hpp"

#define SP_REPORTS 0

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

#if VDEBUG
  assertSplitLevelsExist(cl->splits());
#endif

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

#if SP_REPORTS
  cout<<"Splitting "<<(*cl)<<" into level "<<lev<<", first component "<<(*comp)<<endl;
#endif


  env.statistics->backtrackingSplits++;
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

//  cout<<cl->toString()<<" reduced by "<<premise->toString()<<endl;

#if VDEBUG
  assertSplitLevelsExist(cl->splits());
  assertSplitLevelsExist(premise->splits());
#endif

  SplitSet* diff=premise->splits()->subtract(cl->splits());

#if SP_REPORTS==2
  cout<<"Reduced "<<(*cl)<<" by "<<(*premise)<<". Added to reduced stack on levels "<<diff->toString()<<endl;
#endif

  if(diff->isEmpty()) {
    return;
  }

  cl->incReductionTimestamp();
  ASS(BDD::instance()->isFalse(cl->prop())); //BDDs are disabled when we do backtracking splitting
  SplitSet::Iterator dit(diff);
  while(dit.hasNext()) {
    SplitLevel slev=dit.next();
    _db[slev]->addReduced(cl);
  }
}

void BSplitter::onNewClause(Clause* cl)
{
  CALL("BSplitter::onNewClause");

  if(!cl->splits()) {
    SplitSet* splits=getNewClauseSplitSet(cl);
    assignClauseSplitSet(cl, splits);
#if SP_REPORTS==2
    cout<<"New clause assigned levels: "<<(*cl)<<endl;
#endif
  }
//  cout<<(*cl)<<endl;
#if VDEBUG
  assertSplitLevelsExist(cl->splits());
#endif
}

void BSplitter::SplitRecord::addReduced(Clause* cl)
{
  CALL("BSplitter::SplitRecord::addReduced");

  cl->incRefCnt(); //dec when popped from the '_db[slev]->reduced' stack in backtrack method
  reduced.push(ReductionRecord(cl->getReductionTimestamp(),cl));
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
  res->setAge(cl->age());
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

  Clause::requestAux();
  static RCClauseStack trashed;
  static RCClauseStack restored;
  ASS(restored.isEmpty());

start:
  ASS(trashed.isEmpty());

  Clause* cl=toDo.pop();
  ASS(cl->isEmpty());

  SplitSet* refSplits=cl->splits();
  ASS_G(refSplits->size(),0);

  SplitLevel refLvl=refSplits->maxval(); //refuted level
#if SP_REPORTS
  cout<<"Level "<<refLvl<<" refuted\n";
#endif

  SplitSet* backtracked;
  if(stackSplitting()) {
    NOT_IMPLEMENTED;
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

#if SP_REPORTS
  cout<<"Backtracking on "<<(*cl)<<endl;
  cout<<"base "<<(*_db[refLvl]->base)<<endl;
  cout<<"comp "<<(*_db[refLvl]->component)<<endl;
  cout<<"to be backtracked: "<<backtracked->toString()<<endl;
#endif

  SplitSet* altSplitSet;
  //add the other component of the splitted clause (plus possibly some other clauses)
  getAlternativeClauses(_db[refLvl]->base, _db[refLvl]->component, cl, refLvl, restored, altSplitSet);


  SplitSet::Iterator blit(backtracked);
  while(blit.hasNext()) {
    SplitLevel bl=blit.next();
//    cout<<"scanning level "<<bl<<"\n";
    SplitRecord* sr=_db[bl];

    while(sr->children.isNonEmpty()) {
      Clause* ccl=sr->children.pop();
      if(!ccl->hasAux()) {
	ASS(ccl->splits()->member(bl));
	if(ccl->store()!=Clause::BACKTRACKED) {
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

//    cout<<"backtracking level "<<bl<<"\n";
    Clause* bcl=sr->base;
    if(bl!=refLvl) {
      restored.push(bcl);
    }
    else {
      //If the refutation depended on more split-levels than the base
      //clause, we should restore the base clause when backtracking
      //those extra levels.
      SplitSet* difSet=altSplitSet->subtract(bcl->splits());
      if(!difSet->isEmpty()) {
	SplitSet::Iterator dsit(difSet);
	bcl->incReductionTimestamp();
	while(dsit.hasNext()) {
	  SplitLevel slev=dsit.next();
	  ASS(_db[slev]);
	  _db[slev]->addReduced(bcl);
	}
      }
    }

    while(sr->reduced.isNonEmpty()) {
      ReductionRecord rrec=sr->reduced.pop();
      Clause* rcl=rrec.clause;
      if(rrec.timestamp==rcl->getReductionTimestamp()) {
	restored.push(rcl);
      }
      rcl->decRefCnt(); //inc when pushed on the 'sr->reduced' stack in BSplitter::SplitRecord::addReduced
    }

    _db[bl]=0;
    delete sr;
  }

  while(trashed.isNonEmpty()) {
    Clause* tcl=trashed.popWithoutDec();
    if(tcl->store()!=Clause::NONE) {
      _sa->removeActiveOrPassiveClause(tcl);
      ASS_EQ(tcl->store(), Clause::NONE);
    }
    tcl->setStore(Clause::BACKTRACKED);
    tcl->decRefCnt(); //belongs to trashed.popWithoutDec()
  }

  if(toDo.isNonEmpty()) {
    goto start; //////goto start here///////
  }

  while(restored.isNonEmpty()) {
    Clause* rcl=restored.popWithoutDec();
    if(!rcl->hasAux() && rcl->store()!=Clause::BACKTRACKED) {
      ASS(!rcl->splits()->hasIntersection(backtracked));
      rcl->setAux(0);
      ASS_EQ(rcl->store(), Clause::NONE);
      rcl->incReductionTimestamp();
      rcl->setProp(BDD::instance()->getFalse()); //we asserted it was false in onClauseReduction
      _sa->addNewClause(rcl);
  #if VDEBUG
      //check that restored clause does not depend on splits that were already backtracked
      assertSplitLevelsExist(rcl->splits());
  #endif
#if SP_REPORTS==2
      cout<<"Restored clause "<<(*rcl)<<endl;
#endif

    }
    rcl->decRefCnt(); //belongs to restored.popWithoutDec();
  }

  Clause::releaseAux();

#if SP_REPORTS
  cout<<"-- backtracking done --"<<"\n";
#endif
}

void BSplitter::getAlternativeClauses(Clause* base, Clause* firstComp, Clause* refutation, SplitLevel refLvl,
    RCClauseStack& acc, SplitSet*& altSplitSet)
{
  CALL("BSplitter::getAlternativeClauses");

  Unit::InputType inp=max(base->inputType(), refutation->inputType());

  SplitSet* resSplits=base->splits()->getUnion(refutation->splits())->subtract(SplitSet::getSingleton(refLvl));
  BDDNode* resProp=BDD::instance()->getFalse(); //all BDD resoning is disabled when doing backtracking splitting
  int resAge=base->age();

  altSplitSet=resSplits;

  env.statistics->backtrackingSplitsRefuted++;
  if(resSplits->isEmpty()) {
    env.statistics->backtrackingSplitsRefutedZeroLevel++;
  }


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
  scl->setAge(resAge);
  scl->setProp(resProp);
  assignClauseSplitSet(scl, resSplits);
  acc.push(scl);
#if SP_REPORTS
  cout<<"sp add "<<(*scl)<<endl;
#endif

  if(firstComp->isGround()) {
    //if the first component is ground, add its negation
    Clause::Iterator fcit(*firstComp);
    while(fcit.hasNext()) {
      Literal* glit=fcit.next();
      Inference* ginf=new Inference2(Inference::SPLITTING, base, refutation);
      Clause* gcl=Clause::fromIterator(getSingletonIterator(Literal::oppositeLiteral(glit)), inp, ginf);
      gcl->setAge(resAge);
      gcl->setProp(resProp);
      assignClauseSplitSet(gcl, resSplits);
      acc.push(gcl);
#if SP_REPORTS
      cout<<"sp add "<<(*gcl)<<endl;
#endif
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

  static DHSet<SplitLevel> depSet; //in this set also levels already backtracked can occur
  static LevelStack depStack;
  static LevelStack toDo;
  depSet.reset();
  depStack.reset();
  toDo.reset();

  toDo.push(lev);
  depSet.insert(lev);
  while(toDo.isNonEmpty()) {
    SplitLevel l=toDo.pop();
    if(!_db[l]) {
      continue;
    }
    depStack.push(l);
    LevelStack::Iterator dit(_db[l]->dependent);
    while(dit.hasNext()) {
      SplitLevel dl=dit.next();
      if(!depSet.find(dl)) {
	toDo.push(dl);
	depSet.insert(dl);
      }
    }
  }
  return SplitSet::getFromArray(depStack.begin(), depStack.size());
}

#if VDEBUG

void BSplitter::assertSplitLevelsExist(SplitSet* s)
{
  CALL("BSplitter::assertSplitLevelsExist");

  SplitSet::Iterator sit(s);
  while(sit.hasNext()) {
    SplitLevel lev=sit.next();
    ASS_REP(_db[lev]!=0, lev);
  }
}

#endif

}

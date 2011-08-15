/**
 * @file BSplitter.cpp
 * Implements class BSplitter.
 */

#include "Lib/DHSet.hpp"
#include "Lib/Environment.hpp"
#include "Lib/IntUnionFind.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/SharedSet.hpp"

#include "Kernel/BDD.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/TermIterators.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "BSplitter.hpp"
#include "SaturationAlgorithm.hpp"

/**
 * If set to 1 or 2, details about splitting operations performed will be output
 * (more of them for 2). Otherwise set to 0.
 */
#define SP_REPORTS 0

namespace Saturation
{

using namespace Lib;
using namespace Kernel;

BSplitter::BSplitter()
: _nextLev(1)
{
}

void BSplitter::init(SaturationAlgorithm* sa)
{
  CALL("BSplitter::init");

  Splitter::init(sa);
  _addGroundNegation=getOptions().splitAddGroundNegation();
}

/**
 * Attempt to split clause @b cl, and return true if successful
 *
 * If splitting successful, the first splitting component is added
 * to the saturation algorithm through @b SaturationAlgorithm::addNewClause,
 * and the base clause can be considered to be already reduced
 * (it will be handled as such at the backtracking), so it can be safely
 * removed from the saturation algorithm by the caller.
 */
bool BSplitter::doSplitting(Clause* cl)
{
  CALL("BSplitter::doSplitting");

  if(!splittingAllowed(cl)) {
    return false;
  }

  Clause* comp;
  comp=getComponent(cl);
  if(!comp) {
    return false;
  }
#if VDEBUG
  assertSplitLevelsExist(cl->splits());
#endif

  SplitLevel lev=_nextLev++;
  SplitRecord* sr=new SplitRecord(cl, comp);

  //update "dependent" field of base SplitRecords
  SplitSet::Iterator bsit(cl->splits());
  while(bsit.hasNext()) {
    SplitLevel blev=bsit.next();
    _db[blev]->dependent.push(lev);
  }

  ASS(!_db[lev]);
  _db[lev]=sr;

//  assignClauseSplitSet(comp, cl->splits()->getUnion(SplitSet::getSingleton(lev)));
  assignClauseSplitSet(comp, SplitSet::getSingleton(lev));
  _sa->addNewClause(comp);

#if SP_REPORTS
  cout<<"Splitting "<<(*cl)<<" into level "<<lev<<", first component "<<(*comp)<<endl;
#endif


  env.statistics->backtrackingSplits++;
  return true;
}

/**
 * Register the reduction of the @b cl clause
 */
void BSplitter::onClauseReduction(Clause* cl, ClauseIterator premises, Clause* replacement)
{
  CALL("BSplitter::onClauseReduction");
  ASS(cl);

  if(!premises.hasNext()) {
    ASS(!replacement || cl->splits()==replacement->splits());
    return;
  }

  SplitSet* diff=premises.next()->splits();
  while(premises.hasNext()) {
    Clause* premise=premises.next();
    ASS(premise);
    diff=diff->getUnion(premise->splits());
  }
  if(replacement) {
    diff=diff->getUnion(replacement->splits());
  }
  diff=diff->subtract(cl->splits());
  
#if VDEBUG
  assertSplitLevelsExist(diff);
#endif

#if SP_REPORTS==2
  cout<<"Reduced "<<(*cl)<<". Added to reduced stack on levels {"<<diff->toString()<<"}."<<endl;
#endif

  if(diff->isEmpty()) {
    return;
  }

  cl->incReductionTimestamp();
  //BDDs are disabled when we do backtracking splitting so they can only contain false
  ASS(BDD::instance()->isFalse(cl->prop()));
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

/**
 * Add a reduced clause to the @b SplitRecord object.
 */
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
    VariableIterator vit(lit);
    while(vit.hasNext()) {
      unsigned master=varMasters.findOrInsert(vit.next().var(), i);
      if(master!=i) {
	components.doUnion(master, i);
      }
    }
  }
  components.evalComponents();

  int compCnt=components.getComponentCount();

  if(compCnt==1 || (splitPositive() && posLits<=1)) {
    return 0;
  }

  static Stack<Literal*> lits;

  IntUnionFind::ComponentIterator cit(components);


  for(;;) {
  compAssemblyStart:
    if(!cit.hasNext()) {
      return 0;
    }
    lits.reset();

    IntUnionFind::ElementIterator elit=cit.next();

    unsigned compPosLits=0;
    while(elit.hasNext()) {
      int litIndex=elit.next();
      Literal* lit=(*cl)[litIndex];
      lits.push(lit);
      if(lit->isPositive()) {
	compPosLits++;
      }
      if(isAnswerLiteral(lit)) {
	goto compAssemblyStart; //we don't split out answer literals, so next component has to be attempted
      }
    }
    if(splitPositive()) {
      if(compPosLits==posLits) {
	return 0;
      }
      if(compPosLits==0) {
	continue; //try next component
      }
    }
  }

  Clause* res=Clause::fromStack(lits, cl->inputType(), new Inference(Inference::BACKTRACKING_SPLITTING_COMPONENT));
  res->setAge(cl->age());
  res->initProp(BDD::instance()->getFalse());
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

/**
 * Assign the @b SplitSet @b splits to the clause @b cl.
 */
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

bool BSplitter::handleEmptyClause(Clause* cl)
{
  CALL("BSplitter::handleEmptyClause");

  if(cl->splits()->isEmpty()) {
    return false;
  }
  ASS(BDD::instance()->isFalse(cl->prop()));

  _splitRefutations.push(cl);
  return true;
}

void BSplitter::onAllProcessed()
{
  CALL("BSplitter::onAllProcessed");
  ASS(_sa->clausesFlushed());

  if(_splitRefutations.isNonEmpty()) {
    backtrack(pvi( RCClauseStack::Iterator(_splitRefutations) ));
    _splitRefutations.reset();
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

Inference* BSplitter::getAlternativeClauseInference(Clause* base, Clause* firstComp, Clause* refutation)
{
  CALL("BSplitter::getAlternativeClauseInference");
  ASS_EQ(firstComp->splits()->size(), 1); //the 'definition' clause always has exactly one level in the split history
  ASS_EQ(refutation->length(), 0); //refutation is always an empty clause

  UnitList* premises=0;
  UnitList::push(refutation, premises);
  UnitList::push(firstComp, premises);
  UnitList::push(base, premises);

  return new InferenceMany(Inference::BACKTRACKING_SPLIT_REFUTATION, premises);
}

void BSplitter::getAlternativeClauses(Clause* base, Clause* firstComp, Clause* refutation, SplitLevel refLvl,
    RCClauseStack& acc, SplitSet*& altSplitSet)
{
  CALL("BSplitter::getAlternativeClauses");

  Unit::InputType inp=max(base->inputType(), refutation->inputType());

  SplitSet* resSplits=base->splits()->getUnion(refutation->splits())->subtract(SplitSet::getSingleton(refLvl));
  BDDNode* resProp=BDD::instance()->getFalse(); //all BDD reasoning is disabled when doing backtracking splitting
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
  Inference* sinf=getAlternativeClauseInference(base, firstComp, refutation);
  Clause* scl=Clause::fromStack(secLits, inp, sinf);
  scl->setAge(resAge);
  scl->initProp(resProp);
  assignClauseSplitSet(scl, resSplits);
  acc.push(scl);
  _sa->onParenthood(scl, base);
  _sa->onParenthood(scl, refutation);
#if SP_REPORTS
  cout<<"sp add "<<(*scl)<<endl;
#endif

  if(_addGroundNegation && firstComp->isGround()) {
    //if the first component is ground, add its negation
    SplitSet* gndResSplits=refutation->splits()->subtract(SplitSet::getSingleton(refLvl));
    Clause::Iterator fcit(*firstComp);
    while(fcit.hasNext()) {
      Literal* glit=fcit.next();
      Inference* ginf=getAlternativeClauseInference(base, firstComp, refutation);
      Clause* gcl=Clause::fromIterator(getSingletonIterator(Literal::complementaryLiteral(glit)), inp, ginf);
      gcl->setAge(resAge);
      gcl->initProp(resProp);
      assignClauseSplitSet(gcl, gndResSplits);
      acc.push(gcl);
      _sa->onParenthood(gcl, base);
      _sa->onParenthood(gcl, refutation);
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

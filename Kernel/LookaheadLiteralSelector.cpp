/**
 * @file LookaheadLiteralSelector.cpp
 * Implements class LookaheadLiteralSelector.
 */

#include "Lib/DArray.hpp"
#include "Lib/Exception.hpp"
#include "Lib/Stack.hpp"

#include "Indexing/IndexManager.hpp"
#include "Indexing/LiteralIndex.hpp"
#include "Indexing/LiteralIndexingStructure.hpp"
#include "Indexing/TermIndex.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "EqHelper.hpp"
#include "LiteralComparators.hpp"
#include "Matcher.hpp"
#include "Ordering.hpp"
#include "RobSubstitution.hpp"

#include "LookaheadLiteralSelector.hpp"

#undef LOGGING
#define LOGGING 0

namespace Kernel
{

using namespace Lib;
using namespace Indexing;
using namespace Saturation;

struct LookaheadLiteralSelector::GenIteratorIterator
{
  DECL_ELEMENT_TYPE(VirtualIterator<void>);

  GenIteratorIterator(Literal* lit) : stage(0), lit(lit), prepared(false) {}

  bool hasNext()
  {
    CALL("LookaheadLiteralSelector::GenIteratorIterator::hasNext");

    if(prepared) {
      return true;
    }

    SaturationAlgorithm* salg=SaturationAlgorithm::tryGetInstance();
    ASS(salg); //we are selecting literals only during the run of the saturation algorithm
    IndexManager* imgr=salg->getIndexManager();

  start:
    switch(stage) {
    case 0:  //resolution
    {
      LiteralIndexingStructure* gli=imgr->getGeneratingLiteralIndexingStructure();
      nextIt=pvi( getStaticCastIterator<void>(gli->getUnifications(lit,true,false)) );
      break;
    }
    case 1:  //backward superposition
    {
      TermIndex* bsi=static_cast<TermIndex*>(imgr->get(SUPERPOSITION_SUBTERM_SUBST_TREE));
      nextIt=pvi( getMapAndFlattenIterator(
	       EqHelper::getLHSIterator(lit),
	       TermUnificationRetriever(bsi)) );
      break;
    }
    case 2:  //forward superposition
    {
      TermIndex* fsi=static_cast<TermIndex*>(imgr->get(SUPERPOSITION_LHS_SUBST_TREE));
      nextIt=pvi( getMapAndFlattenIterator(
	       EqHelper::getRewritableSubtermIterator(lit),
	       TermUnificationRetriever(fsi)) );
      break;
    }
    case 3:  //equality resolution
    {
      bool haveEqRes=false;
      if(lit->isNegative() && lit->isEquality()) {
	RobSubstitution rs;
	if(rs.unify(*lit->nthArgument(0), 0, *lit->nthArgument(1), 0)) {
	  haveEqRes=true;
	  nextIt=pvi( getStaticCastIterator<void>(getSingletonIterator(0)) );
	}
      }
      if(!haveEqRes) {
	stage++;
	goto start;
      }
      break;
    }
    default:
      ASSERTION_VIOLATION;
    case 4:  //finish
    {
      prepared=false;
      return false;
    }
    }
    prepared=true;
    return true;
  }

  VirtualIterator<void> next()
  {
    CALL("LookaheadLiteralSelector::GenIteratorIterator::next");
    if(!prepared) {
      ALWAYS(hasNext());
    }
    ASS(prepared);
    prepared=false;
    stage++;
    return nextIt;
  }
private:

  struct TermUnificationRetriever
  {
    TermUnificationRetriever(TermIndex* index) : _index(index) {}
    DECL_RETURN_TYPE(VirtualIterator<void>);
    OWN_RETURN_TYPE operator()(TermList trm)
    {
      return pvi( getStaticCastIterator<void>(_index->getUnifications(trm,false)) );
    }
  private:
    TermIndex* _index;
  };

  int stage;
  Literal* lit;
  bool prepared;
  VirtualIterator<void> nextIt;
};

VirtualIterator<void> LookaheadLiteralSelector::getGeneraingInferenceIterator(Literal* lit)
{
  CALL("LookaheadLiteralSelector::getGeneraingInferenceIterator");

  return pvi( getFlattenedIterator(GenIteratorIterator(lit)) );
}

Literal* LookaheadLiteralSelector::pickTheBest(Literal** lits, unsigned cnt)
{
  CALL("LookaheadLiteralSelector::pickTheBest");
  ASS_G(cnt,1); //special cases are handled elsewhere
  LOG("ptb");

  static DArray<VirtualIterator<void> > runifs; //resolution unification iterators
  runifs.ensure(cnt);

  for(unsigned i=0;i<cnt;i++) {
    runifs[i]=getGeneraingInferenceIterator(lits[i]);
  }

  static Stack<Literal*> candidates;
  candidates.reset();
  do {
    for(unsigned i=0;i<cnt;i++) {
      if(runifs[i].hasNext()) {
	LOGV(*lits[i]);
	runifs[i].next();
      }
      else {
	LOG("no more: "<<(*lits[i]));
	candidates.push(lits[i]);
      }
    }
  } while(candidates.isEmpty());

  using namespace LiteralComparators;
  typedef Composite<ColoredFirst,
	    Composite<NoPositiveEquality,
	    Composite<LeastTopLevelVariables,
	    Composite<LeastDistinctVariables, LexComparator> > > > LitComparator;

  Literal* res=candidates.pop();
  if(candidates.isNonEmpty()) {
    LitComparator comp;
    while(candidates.isNonEmpty()) {
      Literal* lit=candidates.pop();
      if(comp.compare(res, lit)==LESS) {
	res=lit;
      }
    }
  }

  for(unsigned i=0;i<cnt;i++) {
    runifs[i].drop(); //release the iterators
  }
  return res;
}

void LookaheadLiteralSelector::removeVariants(LiteralStack& lits)
{
  CALL("LookaheadLiteralSelector::removeVariants");

  size_t cnt=lits.size();

  for(size_t i=0;i<cnt-1;i++) {
    for(size_t j=i+1;j<cnt;j++) {
      if(MatchingUtils::isVariant(lits[i], lits[j], false)) {
	LOG("variants "<<(*lits[i])<<"    "<<(*lits[j]));
	cnt--;
	swap(lits[j], lits[cnt]);
	lits.pop();
      }
    }
  }
}

void LookaheadLiteralSelector::doSelection(Clause* c, unsigned eligible)
{
  CALL("LookaheadLiteralSelector::doSelection");

  LiteralList* maximals=0;
  Literal* singleSel=0;

  static LiteralStack selectable;
  selectable.reset();

  if(_completeSelection) {
    for(int li=((int)eligible)-1; li>=0; li--) {
      Literal* lit=(*c)[li];
      if(isNegativeForSelection(lit)) {
	selectable.push(lit);
      }
    }

    //figure out which are the maximal literals
    for(int li=((int)eligible)-1; li>=0; li--) {
      Literal* lit=(*c)[li];
      LiteralList::push(lit,maximals);
    }
    Ordering::instance()->removeNonMaximal(maximals);
    ASS(maximals);
    if(selectable.isEmpty()) {
      //there are no negative literals, so we have to select all positiva anyway
      goto selection_done;
    }

    removeVariants(selectable);

    if(!maximals->tail() && isPositiveForSelection(maximals->head())) {
      //There is only one maximal literal and it is positive.
      //therefore we can select either one negative literal, or this one.
      selectable.push(maximals->head());
    }
  }
  else {
    selectable.loadFromIterator(ArrayishObjectIterator<Clause>(*c, eligible));
    removeVariants(selectable);
  }

  if(selectable.size()==1) {
    singleSel=selectable.pop();
    goto selection_done;
  }
  ASS_G(selectable.size(),1);

  LOG("deciding for "<<(*c));
  singleSel=pickTheBest(selectable.begin(), selectable.size());

  LOG("selected "<<(*singleSel)<<" from "<<(*c));

selection_done:
  if(singleSel) {
    maximals->destroy();
    maximals=0;
    LiteralList::push(singleSel,maximals);
  }

  //here we rely on the fact that the @b sel list contains literals
  //in the same order as they appear in the clause
  unsigned selCnt=0;
  for(unsigned li=0; maximals; li++) {
    ASS_L(li,eligible);
    if((*c)[li]==maximals->head()) {
      if(li!=selCnt) {
	swap((*c)[li], (*c)[selCnt]);
      }
      selCnt++;
      LiteralList::pop(maximals);
    }
  }

  ASS(selCnt>0);

  c->setSelected(selCnt);

  ensureSomeColoredSelected(c, eligible);
}

}

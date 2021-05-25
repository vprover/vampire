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

namespace Kernel
{

using namespace Lib;
using namespace Indexing;
using namespace Saturation;

/**
 * Iterator that yields the same number of elements as there are inferences
 * that can be performed with a clause that has the literal passed to
 * the constructor selected
 */
struct LookaheadLiteralSelector::GenIteratorIterator
{
  DECL_ELEMENT_TYPE(VirtualIterator<void>);

  GenIteratorIterator(Literal* lit, LookaheadLiteralSelector& parent) : stage(0), lit(lit), prepared(false), _parent(parent) {}

  bool hasNext()
  {
    CALL("LookaheadLiteralSelector::GenIteratorIterator::hasNext");

    if(prepared) {
      return true;
    }

    SaturationAlgorithm* salg=SaturationAlgorithm::tryGetInstance();
    if(!salg) {
      static bool errAnnounced = false;
      if(!errAnnounced) {
	errAnnounced = true;
	env.beginOutput();
	env.out()<<"Using LookaheadLiteralSelector without having an SaturationAlgorithm object\n";
	env.endOutput();
      }
      //we are too early, there's no saturation algorithm and therefore no generating inferences
      prepared=false;
      return false;
    }

    IndexManager* imgr=salg->getIndexManager();
    ASS(imgr);
  start:
    switch(stage) {
    case 0:  //resolution
    {
      LiteralIndexingStructure* gli=imgr->getGeneratingLiteralIndexingStructure();
      if(!gli) { stage++; goto start; }

      nextIt=pvi( getStaticCastIterator<void>(gli->getUnifications(lit,true,false)) );
      break;
    }
    case 1:  //backward superposition
    {
      if(!imgr->contains(SUPERPOSITION_SUBTERM_SUBST_TREE)) { stage++; goto start; }
      TermIndex* bsi=static_cast<TermIndex*>(imgr->get(SUPERPOSITION_SUBTERM_SUBST_TREE));
      ASS(bsi);

      nextIt=pvi( getMapAndFlattenIterator(
	       EqHelper::getLHSIterator(lit, _parent._ord),
	       TermUnificationRetriever(bsi)) );
      break;
    }
    case 2:  //forward superposition
    {
      if(!imgr->contains(SUPERPOSITION_LHS_SUBST_TREE)) { stage++; goto start; }
      TermIndex* fsi=static_cast<TermIndex*>(imgr->get(SUPERPOSITION_LHS_SUBST_TREE));
      ASS(fsi);

      nextIt=pvi( getMapAndFlattenIterator(
	       EqHelper::getSubtermIterator(lit, _parent._ord), //TODO update for combinatory sup
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
    VirtualIterator<void> operator()(TermList trm)
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

  LookaheadLiteralSelector& _parent;
};

/**
 * Return iterator with the same number of elements as there are inferences
 * that can be performed with @b lit literal selected
 */
VirtualIterator<void> LookaheadLiteralSelector::getGeneraingInferenceIterator(Literal* lit)
{
  CALL("LookaheadLiteralSelector::getGeneraingInferenceIterator");

  return pvi( getFlattenedIterator(GenIteratorIterator(lit, *this)) );
}

/**
 * Return the literal from the @b lits array (of length @b cnt) that
 * is the best to be selected. This selection is done irregardless any
 * completeness constraints, the caller has to handle that, if necessary.
 */
Literal* LookaheadLiteralSelector::pickTheBest(Literal** lits, unsigned cnt)
{
  CALL("LookaheadLiteralSelector::pickTheBest");
  ASS_G(cnt,1); //special cases are handled elsewhere

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
	runifs[i].next();
      }
      else {
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

/**
 * From the stack @b lits remove literals that are variants of each other
 */
void LookaheadLiteralSelector::removeVariants(LiteralStack& lits)
{
  CALL("LookaheadLiteralSelector::removeVariants");

  size_t cnt=lits.size();

  for(size_t i=0;i<cnt-1;i++) {
    for(size_t j=i+1;j<cnt;j++) {
      if(MatchingUtils::isVariant(lits[i], lits[j], false)) {
	cnt--;
	swap(lits[j], lits[cnt]);
	lits.pop();
      }
    }
  }
}

/**
 * Perform clause selection on the first @b eligible literals of
 * clause @b c
 */
void LookaheadLiteralSelector::doSelection(Clause* c, unsigned eligible)
{
  CALL("LookaheadLiteralSelector::doSelection");

  if(_startupSelector){
   
    _startupSelector->select(c,eligible);

    _skipped++;
    if(_skipped == _delay){
      delete _startupSelector;
      _startupSelector=0;
    }
    return;
  }

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
    _ord.removeNonMaximal(maximals);
    ASS(maximals);
    if(selectable.isEmpty()) {
      //there are no negative literals, so we have to select all positive anyway
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

  singleSel=pickTheBest(selectable.begin(), selectable.size());

selection_done:
  if(singleSel) {
    LiteralList::destroy(maximals);
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

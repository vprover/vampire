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
#include "Lib/Metaiterators.hpp"
#include "Lib/Stack.hpp"

#include "Indexing/IndexManager.hpp"
#include "Indexing/LiteralIndex.hpp"
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

// estimate the number of inferences that can be performed with `lit` under `ord`
static size_t estimateNumberOfInferences(Literal *lit, const Ordering &ord) {
  using TermIndex = Indexing::TermIndex<TermLiteralClause>;

  size_t total = 0;

  SaturationAlgorithm *salg = SaturationAlgorithm::tryGetInstance();
  ASS(salg)
  IndexManager* imgr=salg->getIndexManager();
  ASS(imgr);

  // resolution
  if(imgr->contains(BINARY_RESOLUTION_SUBST_TREE)) {
    auto bri = static_cast<BinaryResolutionIndex *>(imgr->get(BINARY_RESOLUTION_SUBST_TREE));
    total += countIteratorElements(bri->getUnifications(lit,true,false));
  }

  // backward superposition
  if(imgr->contains(SUPERPOSITION_SUBTERM_SUBST_TREE)) {
    auto ti = static_cast<TermIndex *>(imgr->get(SUPERPOSITION_SUBTERM_SUBST_TREE));
    total += countIteratorElements(getMapAndFlattenIterator(
      EqHelper::getLHSIterator(lit, ord),
      [ti](TypedTermList trm) { return ti->getUnifications(trm, /* retrieveSubst */ false); }
    ));
  }

  // forward superposition
  if(imgr->contains(SUPERPOSITION_LHS_SUBST_TREE)) {
    auto ti = static_cast<TermIndex* >(imgr->get(SUPERPOSITION_LHS_SUBST_TREE));
    total += countIteratorElements(getMapAndFlattenIterator(
      EqHelper::getSubtermIterator(lit, ord), //TODO update for HO superposition
      [ti](TypedTermList trm) { return ti->getUnifications(trm, /* retrieveSubst */ false); }
    ));
  }

  // equality resolution
  if(lit->isNegative() && lit->isEquality()) {
    RobSubstitution rs;
    total += rs.unify(lit->termArg(0), 0, lit->termArg(1), 0);
  }

  return total;
}

/**
 * Return the literal from the @b lits array (of length @b cnt) that
 * is the best to be selected. This selection is done regardless any
 * completeness constraints, the caller has to handle that, if necessary.
 */
Literal* LookaheadLiteralSelector::pickTheBest(Literal** lits, unsigned cnt)
{
  ASS_G(cnt,1); //special cases are handled elsewhere

  // find all minimal candidate literals,
  // according to an estimate of how many inferences they produce
  size_t minInferences = std::numeric_limits<size_t>::max();
  static Stack<Literal*> candidates;
  candidates.reset();
  for(unsigned i = 0; i < cnt; i++) {
    size_t estimate = estimateNumberOfInferences(lits[i], _ord);
    // new minimum
    if(estimate < minInferences) {
      candidates.reset();
      minInferences = estimate;
    }
    // add to minimal candidates
    if(estimate == minInferences)
      candidates.push(lits[i]);
  }

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
  return res;
}

/**
 * From the stack @b lits remove literals that are variants of each other
 */
void LookaheadLiteralSelector::removeVariants(LiteralStack& lits)
{
  size_t cnt=lits.size();

  for(size_t i=0;i<cnt-1;i++) {
    for(size_t j=i+1;j<cnt;j++) {
      if(MatchingUtils::isVariant(lits[i], lits[j], false)) {
        cnt--;
        std::swap(lits[j], lits[cnt]);
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
    selectable.loadFromIterator(arrayIter(*c, eligible));
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
        std::swap((*c)[li], (*c)[selCnt]);
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

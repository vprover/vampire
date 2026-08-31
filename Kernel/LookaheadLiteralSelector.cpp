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

using namespace std;
using namespace Lib;
using namespace Indexing;
using namespace Saturation;

/**
 * Return iterator with the same number of elements as there are inferences
 * that can be performed with @b lit literal selected
 */
VirtualIterator<std::tuple<>> LookaheadLiteralSelector::getGeneraingInferenceIterator(Literal* lit)
{
  return pvi(generatingInferences(lit));
}

/**
 * Yield one (empty) element for each inference that could be performed with a clause
 * that has @b lit selected. Only the *number* of elements matters -- see pickTheBest,
 * which races these iterators against each other and stops as soon as one runs dry, so
 * the elements themselves are never inspected and the substitutions are not retrieved.
 *
 * Being a coroutine matters here beyond readability: the index handles below are frame
 * locals, so each stays alive for exactly as long as the query walking into it. In the
 * hand-written state machine they were locals of hasNext() that died at the end of their
 * case block, while the iterator they had been queried from lived on -- which only
 * worked because the IndexManager keeps the index alive independently.
 */
Generator<std::tuple<>> LookaheadLiteralSelector::generatingInferences(Literal* lit)
{
  ASS(!env.higherOrder());

  SaturationAlgorithm* salg=SaturationAlgorithm::tryGetInstance();
  if(!salg) {
    static bool errAnnounced = false;
    if(!errAnnounced) {
      errAnnounced = true;
      std::cout<<"Using LookaheadLiteralSelector without having an SaturationAlgorithm object\n";
    }
    //we are too early, there's no saturation algorithm and therefore no generating inferences
    co_return;
  }

  //resolution
  if(auto gli = salg->tryGetGeneratingIndex<BinaryResolutionIndex>())
    for([[maybe_unused]] auto qr : iterTraits(gli->getUnifications(lit, /* complementary */ true, /* retrieveSubst */ false)))
      co_yield {};

  //backward superposition
  if(auto bsi = salg->tryGetGeneratingIndex<SuperpositionSubtermIndex</*higherOrder=*/false>>())
    for(TypedTermList lhs : iterTraits(EqHelper::getLHSIterator(lit, _ord)))
      for([[maybe_unused]] auto qr : iterTraits(bsi->getUnifications(lhs, /* retrieveSubst */ false)))
        co_yield {};

  //forward superposition
  if(auto fsi = salg->tryGetGeneratingIndex<SuperpositionLHSIndex>())
    //TODO update for HO superposition
    for(Term* trm : iterTraits(EqHelper::getSubtermIterator</*higherOrder=*/false>(lit, _ord)))
      for([[maybe_unused]] auto qr : iterTraits(fsi->getUnifications(TypedTermList(trm), /* retrieveSubst */ false)))
        co_yield {};

  //equality resolution
  if(lit->isNegative() && lit->isEquality()) {
    RobSubstitution rs;
    if(rs.unify(*lit->nthArgument(0), 0, *lit->nthArgument(1), 0))
      co_yield {};
  }
}

/**
 * Return the literal from the @b lits array (of length @b cnt) that
 * is the best to be selected. This selection is done regardless any
 * completeness constraints, the caller has to handle that, if necessary.
 */
Literal* LookaheadLiteralSelector::pickTheBest(Literal** lits, unsigned cnt)
{
  ASS_G(cnt,1); //special cases are handled elsewhere

  static DArray<VirtualIterator<std::tuple<>> > runifs; //resolution unification iterators
  runifs.ensure(cnt);

  for(unsigned i=0;i<cnt;i++) {
    runifs[i]=getGeneraingInferenceIterator(lits[i]);
  }

  /*
   * MR: the above thing looks like a crazy way to estimate which literal
   * generate least inferences and that a loop returning size_t would be better.
   *
   * However, the trick here is that the iterators compute the inferences _lazily_,
   * and so saves some effort in the common case where there is one clear winner.
   */
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
    runifs[i] = VirtualIterator<std::tuple<>>(); // properly releases _core via move-assign
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

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

#include "Saturation/SaturationAlgorithm.hpp"

#include "LiteralComparators.hpp"
#include "Matcher.hpp"
#include "Ordering.hpp"

#include "LookaheadLiteralSelector.hpp"

#undef LOGGING
#define LOGGING 0

namespace Kernel
{

using namespace Lib;
using namespace Indexing;
using namespace Saturation;

Literal* LookaheadLiteralSelector::pickTheBest(Literal** lits, unsigned cnt)
{
  CALL("LookaheadLiteralSelector::pickTheBest");
  ASS_G(cnt,1); //special cases are handled elsewhere
  LOG("ptb");

  SaturationAlgorithm* salg=SaturationAlgorithm::tryGetInstance();
  ASS(salg); //we are selecting literals only during the run of the saturation algorithm

  LiteralIndexingStructure* gli=salg->getIndexManager()->getGeneratingLiteralIndexingStructure();

  static DArray<SLQueryResultIterator> runifs; //resolution unification iterators
  runifs.ensure(cnt);

  for(unsigned i=0;i<cnt;i++) {
    runifs[i]=gli->getUnifications(lits[i],true,false);
  }

  int iterationLimit=100;

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
    iterationLimit--;
  } while(iterationLimit && candidates.isEmpty());

  if(candidates.isEmpty()) {
    candidates.loadFromIterator(ArrayishObjectIterator<Literal**>(lits, cnt));
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

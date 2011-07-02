/**
 * @file LiteralSelector.cpp
 * Implements class LiteralSelector for literal selection
 */

#include "Lib/Environment.hpp"
#include "Lib/Exception.hpp"

#include "Shell/Options.hpp"

#include "Clause.hpp"
#include "Signature.hpp"
#include "Term.hpp"

#include "LiteralSelector.hpp"

#include "MaximalLiteralSelector.hpp"
#include "BestLiteralSelector.hpp"
#include "LookaheadLiteralSelector.hpp"

#include "LiteralComparators.hpp"


namespace Kernel
{

/**
 * If set to true, the polarity for non-equality literals is
 * considered to be reversed for the purposes of literal selection
 */
bool LiteralSelector::_reversePolarity=false;

#if VDEBUG

/**
 * Counter of existing LiteralSelector instances
 *
 * As we use the @b _reversePolarity static variable in the selector
 * setting, we want always at most one instance to exist.
 */
int LiteralSelector::_instCtr=0;

#endif

/**
 * The selection will be performed among the literals with the
 * highest selection priority in the clause
 */
int LiteralSelector::getSelectionPriority(Literal* l)
{
  Signature::Symbol* psym=env.signature->getPredicate(l->functor());
  if(psym->swbName()) {
    if(l->isPositive() && env.options->splittingWithBlocking()) {
      return 1;
    }
    return -1;
  }
  if(psym->cfName() || psym->answerPredicate()) {
    return -2;
  }
  return 0;
}

/**
 * Return a literal selector object corresponding to number @b num
 *
 * It is expected that this function will be called at most once in
 * the run of Vampre process (see @b _instCtr documentation).
 *
 * The supported literal selector numbers should correspond to numbers
 * allowed in @b Shell::Options::setSelection.
 */
LiteralSelector* LiteralSelector::getSelector(int num)
{
  CALL("LiteralSelector::getSelector");

  using namespace LiteralComparators;

  typedef Composite<ColoredFirst,
	    Composite<MaximalSize,
	    LexComparator> > Comparator2;

  typedef Composite<ColoredFirst,
	    Composite<NoPositiveEquality,
	    Composite<LeastTopLevelVariables,
	    Composite<LeastDistinctVariables, LexComparator> > > > Comparator3;

  typedef Composite<ColoredFirst,
	    Composite<NoPositiveEquality,
	    Composite<LeastTopLevelVariables,
	    Composite<LeastVariables,
	    Composite<MaximalSize, LexComparator> > > > > Comparator4;

  typedef Composite<ColoredFirst,
	    Composite<NegativeEquality,
	    Composite<MaximalSize,
	    Composite<Negative, LexComparator> > > > Comparator10;

#if VDEBUG
  ASS_EQ(_instCtr,0);
#endif
  _reversePolarity=num<0;
  if(num<0) {
    num=-num;
  }

  switch(num) {
  case 0: return new TotalLiteralSelector();
  case 1: return new MaximalLiteralSelector();
  case 2: return new CompleteBestLiteralSelector<Comparator2>();
  case 3: return new CompleteBestLiteralSelector<Comparator3>();
  case 4: return new CompleteBestLiteralSelector<Comparator4>();
  case 10: return new CompleteBestLiteralSelector<Comparator10>();

  case 11: return new LookaheadLiteralSelector(true);

  case 1002: return new BestLiteralSelector<Comparator2>();
  case 1003: return new BestLiteralSelector<Comparator3>();
  case 1004: return new BestLiteralSelector<Comparator4>();
  case 1010: return new BestLiteralSelector<Comparator10>();

  case 1011: return new LookaheadLiteralSelector(false);

  default:
    INVALID_OPERATION("Undefined selection function");
  }
}

/**
 * If there is a colored literal among the first @b eligible
 * ones, ensure at least one colored literal is selected
 */
void LiteralSelector::ensureSomeColoredSelected(Clause* c, unsigned eligible)
{
  CALL("LiteralSelector::ensureSomeColoredSelected");

  if(c->color()==COLOR_TRANSPARENT) {
    //if no literal is colored, do nothing
    return;
  }

  unsigned selCnt=c->selected();

  for(unsigned i=0;i<selCnt;i++) {
    if((*c)[i]->color()!=COLOR_TRANSPARENT) {
      return;
    }
  }

  for(unsigned i=selCnt;i<eligible;i++) {
    if((*c)[i]->color()!=COLOR_TRANSPARENT) {
      swap((*c)[selCnt], (*c)[i]);
      c->setSelected(selCnt+1);
      return;
    }
  }
  //the colored literals are not among the eligible ones
  ASS_L(eligible, c->length());
}

/**
 * Perform literal selection on clause @b c
 *
 * First the literals eligible for selection are determined through
 * the @b getSelectionPriority function, and then the function
 * @b doSelection is called if there is more than one eligible
 * literal.
 */
void LiteralSelector::select(Clause* c)
{
  CALL("LiteralSelector::select");

  unsigned clen=c->length();

  if(clen<=1) {
    c->setSelected(clen);
    return;
  }

  unsigned eligible=1;
  int maxPriority=getSelectionPriority((*c)[0]);
  bool modified=false;

  for(unsigned i=1;i<clen;i++) {
    int priority=getSelectionPriority((*c)[i]);
    if(priority==maxPriority) {
      if(eligible!=i) {
	swap((*c)[i],(*c)[eligible]);
	modified=true;
      }
      eligible++;
    }
    else if(priority>maxPriority) {
      maxPriority=priority;
      eligible=1;
      swap((*c)[i],(*c)[0]);
      modified=true;
    }
  }
  ASS_LE(eligible,clen);
  if(modified) {
    c->notifyLiteralReorder();
  }

  if(eligible==1) {
    c->setSelected(eligible);
    return;
  }

  ASS_G(eligible,1);
  doSelection(c, eligible);
}

/**
 * Select all eligible literals in clause @b c
 */
void TotalLiteralSelector::doSelection(Clause* c, unsigned eligible)
{
  CALL("TotalLiteralSelector::doSelection");

  c->setSelected(eligible);
}

}

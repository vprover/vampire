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
#include "SpassLiteralSelector.hpp"
#include "ELiteralSelector.hpp"

#include "LiteralComparators.hpp"

#undef LOGGING
#define LOGGING 0

namespace Kernel
{

/**
 * Array that for each predicate contains bol value determining whether
 * the polarity of the predicate should be reversed for the purposes of
 * literal selection
 */
ZIArray<bool> LiteralSelector::_reversePredicate;


/**
 * Return true if literal @b l is positive for the purpose of
 * literal selection
 *
 * This function is to allow for easy implementation of
 * selection functions with negative numbers. Those functions
 * consider all literals except for equality to be of
 * opposite polarity.
 */
bool LiteralSelector::isPositiveForSelection(Literal* l) const
{
  if(l->isEquality()) {
    return l->isPositive(); //we don't change polarity for equality
  }
  unsigned pred = l->functor();
  return l->isPositive() ^ _reversePolarity ^ _reversePredicate[pred];
}

void LiteralSelector::reversePredicatePolarity(unsigned pred, bool reverse)
{
  CALL("reversePredicatePolarity");
  ASS(pred!=0 || !reverse); //we never reverse polarity of equality

  _reversePredicate[pred] = reverse;
}

/**
 * The selection will be performed among the literals with the
 * highest selection priority in the clause
 */
int LiteralSelector::getSelectionPriority(Literal* l) const
{
  CALL("LiteralSelector::getSelectionPriority");

  Signature::Symbol* psym=env.signature->getPredicate(l->functor());
  if(psym->label() || psym->answerPredicate()) {
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
LiteralSelector* LiteralSelector::getSelector(const Ordering& ordering, const Options& options, int selectorNumber)
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

  int absNum = abs(selectorNumber);

  LiteralSelector* res;
  switch(absNum) {
  case 0: res = new TotalLiteralSelector(ordering, options); break;
  case 1: res = new MaximalLiteralSelector(ordering, options); break;
  case 2: res = new CompleteBestLiteralSelector<Comparator2>(ordering, options); break;
  case 3: res = new CompleteBestLiteralSelector<Comparator3>(ordering, options); break;
  case 4: res = new CompleteBestLiteralSelector<Comparator4>(ordering, options); break;
  case 10: res = new CompleteBestLiteralSelector<Comparator10>(ordering, options); break;

  case 11: res = new LookaheadLiteralSelector(true, ordering, options); break;

  case 20:
  case 21:
  case 22:
    res = new SpassLiteralSelector(ordering, options,static_cast<SpassLiteralSelector::Values>(absNum-20));
    break;

  case 30:
  case 31:
  case 32:
  case 33:
  case 34:
  case 35:
    res = new ELiteralSelector(ordering, options,static_cast<ELiteralSelector::Values>(absNum-30));
    break;

  case 1002: res = new BestLiteralSelector<Comparator2>(ordering, options); break;
  case 1003: res = new BestLiteralSelector<Comparator3>(ordering, options); break;
  case 1004: res = new BestLiteralSelector<Comparator4>(ordering, options); break;
  case 1010: res = new BestLiteralSelector<Comparator10>(ordering, options); break;

  case 1011: res = new LookaheadLiteralSelector(false, ordering, options); break;

  default:
    INVALID_OPERATION("Undefined selection function");
  }
  if(selectorNumber<0) {
    res->_reversePolarity = true;
  }
  return res;
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

  unsigned selCnt=c->numSelected();

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

  ASS(eligible < c->length() || //the colored literals are not among the eligible ones ...
      c->splits());             // .. unless the color comes from the propositional part
}

/**
 * Perform literal selection on clause @b c
 *
 * First the literals eligible for selection are determined through
 * the @b getSelectionPriority function, and then the function
 * @b doSelection is called if there is more than one eligible
 * literal.
 */
void LiteralSelector::select(Clause* c, unsigned eligibleInp)
{
  CALL("LiteralSelector::select");
  ASS_LE(eligibleInp, c->length());

  if(eligibleInp==0) {
    eligibleInp = c->length();
  }

  if(eligibleInp<=1) {
    c->setSelected(eligibleInp);
    return;
  }

  unsigned eligible=1;
  int maxPriority=getSelectionPriority((*c)[0]);
  bool modified=false;

  for(unsigned i=1;i<eligibleInp;i++) {
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
  ASS_LE(eligible,eligibleInp);
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

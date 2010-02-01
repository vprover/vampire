/**
 * @file LiteralSelector.cpp
 * Implements class LiteralSelector for literal selection
 */

#include "../Lib/Exception.hpp"

#include "Term.hpp"
#include "Clause.hpp"

#include "LiteralSelector.hpp"

#include "MaximalLiteralSelector.hpp"

#include "BestLiteralSelector.hpp"
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

LiteralSelector* LiteralSelector::getSelector(int num)
{
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

  case 1002: return new BestLiteralSelector<Comparator2>();
  case 1003: return new BestLiteralSelector<Comparator3>();
  case 1004: return new BestLiteralSelector<Comparator4>();

  case 1010: return new BestLiteralSelector<Comparator10>();
  default:
    INVALID_OPERATION("Undefined selection function");
  }
}

void LiteralSelector::ensureSomeColoredSelected(Clause* c)
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

  unsigned clen=c->length();

  for(unsigned i=selCnt;i<clen;i++) {
    if((*c)[i]->color()!=COLOR_TRANSPARENT) {
      swap((*c)[selCnt], (*c)[i]);
      c->setSelected(selCnt+1);
      return;
    }
  }
  ASSERTION_VIOLATION;
}


void TotalLiteralSelector::select(Clause* c)
{
  CALL("EagerLiteralSelector::select");

  c->setSelected(c->length());
}

}

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

LiteralSelector* LiteralSelector::getSelector(int num)
{
  using namespace LiteralComparators;

  typedef Composite<MaximalSize,
	    LexComparator> Comparator2;

  typedef Composite<NoPositiveEquality,
	    Composite<LeastTopLevelVariables,
	    Composite<LeastDistinctVariables, LexComparator> > > Comparator3;

  typedef Composite<NoPositiveEquality,
	    Composite<LeastTopLevelVariables,
	    Composite<LeastVariables,
	    Composite<MaximalSize, LexComparator> > > > Comparator4;

  typedef Composite<NegativeEquality,
	    Composite<MaximalSize,
	    Composite<Negative, LexComparator> > > Comparator10;


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
    USER_ERROR("Undefined selection function");
  }
}

//MultiColumnMap<Literal*>* LiteralSelector::getLiteralDetailStore()
//{
//  static MultiColumnMap<Literal*> map;
//  return &map;
//}


void TotalLiteralSelector::select(Clause* c)
{
  CALL("EagerLiteralSelector::select");

  c->setSelected(c->length());
}

}

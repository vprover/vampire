/**
 * @file LiteralSelection.cpp
 * Implements class LiteralSelection for literal selection
 */

#include "../Lib/Exception.hpp"

#include "Term.hpp"
#include "Clause.hpp"

#include "LiteralSelector.hpp"

#include "BestLiteralSelector.hpp"
#include "LiteralComparators.hpp"


namespace Kernel
{

LiteralSelector* LiteralSelector::getSelector(int num)
{
  using namespace LiteralComparators;

  typedef Composite<NoPositiveEquality, Composite<LeastTopLevelVariables, MaximalSize> > Comparator10;

  switch(num) {
  case 0: return new TotalLiteralSelector();

  case 10: return new CompleteBestLiteralSelector<Comparator10>();

  case 1010: return new BestLiteralSelector<Comparator10>();

  default:
    USER_ERROR("Undefined selection function");
  }
}

void TotalLiteralSelector::select(Clause* c)
{
  CALL("EagerLiteralSelector::select");

  c->setSelected(c->length());
}

}

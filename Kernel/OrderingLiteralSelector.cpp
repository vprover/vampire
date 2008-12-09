/**
 * @file OrderingLiteralSelector.cpp
 * Implements class OrderingLiteralSelector.
 */


#include "../Lib/List.hpp"

#include "Term.hpp"
#include "Clause.hpp"

#include "OrderingLiteralSelector.hpp"

using namespace Lib;
using namespace Kernel;

void OrderingLiteralSelector::select(Clause* c)
{
  CALL("OrderingLiteralSelector::select");

  unsigned seli;
  //we assume, that weight of a literal is always greater than zero
  unsigned selWeight=0;
  unsigned clen=c->length();

  for(unsigned i=0;i<clen;i++) {
    if((*c)[i]->isNegative() && (!selWeight || (*c)[i]->weight()<selWeight)) {
      seli=i;
      selWeight=(*c)[i]->weight();
    }
  }

  if(selWeight) {
    std::swap((*c)[0], (*c)[seli]);
    c->setSelected(1);
  } else {
    selectPositive(c);
  }

}

void OrderingLiteralSelector::selectPositive(Clause* c)
{
  unsigned clen=c->length();
  LiteralList* sel=0;
  unsigned selCnt=clen;

  for(unsigned li=0;li<clen;li++) {
    LiteralList::push((*c)[li],sel);
  }

  LiteralList** ptr1=&sel;
  while(*ptr1) {
    LiteralList** ptr2=&(*ptr1)->tailReference();
    while(*ptr2) {
      Ordering::Result res=_ord->compare((*ptr1)->head(), (*ptr2)->head());
      //TODO: finish
      ptr2=&(*ptr2)->tailReference();
    }
    ptr1=&(*ptr1)->tailReference();
  }
  c->setSelected(c->length());
}

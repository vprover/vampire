/**
 * @file OrderingLiteralSelector.cpp
 * Implements class OrderingLiteralSelector.
 */

#include <algorithm>

#include "../Lib/List.hpp"

#include "Term.hpp"
#include "Clause.hpp"

#include "OrderingLiteralSelector.hpp"

using namespace std;
using namespace Lib;
using namespace Kernel;

void OrderingLiteralSelector::select(Clause* c)
{
  CALL("OrderingLiteralSelector::select");

  unsigned seli;
  //we assume, that weight of a literal is always greater than zero
  unsigned selWeight=0;
  unsigned clen=c->length();

  if(clen<=1) {
    c->setSelected(clen);
    return;
  }

  for(unsigned i=0;i<clen;i++) {
    if((*c)[i]->isNegative() && ((*c)[i]->weight()>selWeight)) {
//    if((*c)[i]->isNegative() && (!selWeight || (*c)[i]->weight()<selWeight)) {
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

  ASS(clen<=0x7FFFFFFF);
  for(int li=(int)clen-1; li>=0; li--) {
    LiteralList::push((*c)[li],sel);
  }

  _ord->removeNonMaximal(sel);

  unsigned selCnt=0;

  for(unsigned li=0; sel; li++) {
    ASS(li<clen);
    if((*c)[li]==sel->head()) {
      if(li!=selCnt) {
	swap((*c)[li], (*c)[selCnt]);
      }
      selCnt++;
      LiteralList::pop(sel);
    }
  }

  ASS(selCnt>0);

  c->setSelected(selCnt);
}

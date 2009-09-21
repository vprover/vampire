/**
 * @file MaximalLiteralSelector.cpp
 * Implements class MaximalLiteralSelector.
 */

#include <algorithm>

#include "../Lib/List.hpp"

#include "Term.hpp"
#include "Clause.hpp"

#include "MaximalLiteralSelector.hpp"

using namespace std;
using namespace Lib;
using namespace Kernel;

void MaximalLiteralSelector::select(Clause* c)
{
  CALL("OrderingLiteralSelector::select");

  unsigned clen=c->length();
  LiteralList* sel=0;
  bool anyNegative=false;

  for(int li=(int)clen-1; li>=0; li--) {
    if((*c)[li]->isNegative()) {
      anyNegative=true;
      break;
    }
  }
  for(int li=(int)clen-1; li>=0; li--) {
    if(!anyNegative || (*c)[li]->isNegative()) {
      LiteralList::push((*c)[li],sel);
    }
  }

  _ord->removeNonMaximal(sel);

  Literal* singleSel=0;

  LiteralList::Iterator sit(sel);
  while(sit.hasNext()) {
    Literal* sl=sit.next();
    if(sl->isNegative()) {
      singleSel=sl;
      break;
    }
  }
  if(singleSel) {
    sel->destroy();
    sel=0;
    LiteralList::push(singleSel,sel);
  }

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

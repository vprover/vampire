/**
 * @file MaximalLiteralSelector.cpp
 * Implements class MaximalLiteralSelector.
 */

#include <algorithm>

#include "Lib/List.hpp"

#include "Term.hpp"
#include "Clause.hpp"

#include "MaximalLiteralSelector.hpp"

using namespace std;
using namespace Lib;
using namespace Kernel;

void MaximalLiteralSelector::doSelection(Clause* c, unsigned eligible)
{
  CALL("MaximalLiteralSelector::doSelection");

  LiteralList* sel=0;
  bool anyNegative=false;

  for(int li=((int)eligible)-1; li>=0; li--) {
    Literal* lit=(*c)[li];
    if(isNegativeForSelection(lit)) {
      anyNegative=true;
      break;
    }
  }
  for(int li=((int)eligible)-1; li>=0; li--) {
    Literal* lit=(*c)[li];
    if(!anyNegative || isNegativeForSelection(lit)) {
      LiteralList::push(lit,sel);
    }
  }

  _ord->removeNonMaximal(sel);

  Literal* singleSel=0;

  LiteralList::Iterator sit(sel);
  while(sit.hasNext()) {
    Literal* sl=sit.next();
    if(isNegativeForSelection(sl)) {
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
    ASS(li<eligible);
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

  ensureSomeColoredSelected(c, eligible);
}

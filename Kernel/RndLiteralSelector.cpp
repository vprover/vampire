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
 * @file RndLiteralSelector.cpp
 * Implements class RndLiteralSelector.
 */

#include <algorithm>

#include "Lib/List.hpp"
#include "Lib/Random.hpp"

#include "Term.hpp"
#include "Clause.hpp"

#include "RndLiteralSelector.hpp"

using namespace std;
using namespace Lib;
using namespace Kernel;

LiteralList* RndLiteralSelector::getMaximalsInOrder(Clause* c, unsigned eligible)
{
  CALL("RndLiteralSelector::getMaximalsInOrder");

  LiteralList* res = LiteralList::empty();

  for(int li=((int)eligible)-1; li>=0; li--) {
    LiteralList::push((*c)[li],res);
  }

  _ord.removeNonMaximal(res);

  return res;
}

void RndLiteralSelector::doSelection(Clause* c, unsigned eligible)
{
  CALL("RndLiteralSelector::doSelection");

  LiteralList* sel = LiteralList::empty();
  Literal* singleSel = nullptr;

  if (!_complete) {
    singleSel = (*c)[Random::getInteger(eligible)];
  } else {
    int cntNeg = 0;
    LiteralList* neg = LiteralList::empty();
    // collect in sel the literals negative for selection
    for(int li=((int)eligible)-1; li>=0; li--) {
      Literal* lit=(*c)[li];
      if(isNegativeForSelection(lit)) {
        LiteralList::push(lit,neg);
        cntNeg++;
      }
    }
    if (cntNeg > 0 && Random::getBit() /*allow sometimes selecting maximals, even when there are negative*/) {
      singleSel = LiteralList::nth(neg,Random::getInteger(cntNeg));
    } else { // there are no negative literals (or we don't want them), so we take the maximal ones to be complete
      sel = getMaximalsInOrder(c,eligible);
      ASS(LiteralList::isNonEmpty(sel));
    }
  }

  if(singleSel) {
    ASS(LiteralList::isEmpty(sel));
    LiteralList::push(singleSel,sel);
  }
  ASS(LiteralList::isNonEmpty(sel));

  unsigned selCnt=0;

  for (unsigned li = 0; sel; li++) {
    ASS(li < eligible);
    if ((*c)[li] == sel->head()) {
      if (li != selCnt) {
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

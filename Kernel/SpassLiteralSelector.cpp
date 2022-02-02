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
 * @file SpassLiteralSelector.cpp
 * Implements class SpassLiteralSelector.
 */

#include <algorithm>

#include "Lib/List.hpp"

#include "Term.hpp"
#include "Clause.hpp"

#include "SpassLiteralSelector.hpp"

using namespace std;
using namespace Lib;
using namespace Kernel;

LiteralList* SpassLiteralSelector::getMaximalsInOrder(Clause* c, unsigned eligible)
{
  CALL("SpassLiteralSelector::getMaximalsInOrder");

  LiteralList* res = LiteralList::empty();

  for(int li=((int)eligible)-1; li>=0; li--) {
    LiteralList::push((*c)[li],res);
  }

  _ord.removeNonMaximal(res);

  return res;
}

void SpassLiteralSelector::doSelection(Clause* c, unsigned eligible)
{
  CALL("SpassLiteralSelector::doSelection");

  LiteralList* maximals = LiteralList::empty();

  if (_value == IFSEVERALMAXIMAL) {
    maximals = getMaximalsInOrder(c,eligible);
    ASS(LiteralList::isNonEmpty(maximals));
  }

  Literal* singleSel = nullptr;

  if (_value != OFF &&
      (_value != IFSEVERALMAXIMAL || LiteralList::isNonEmpty(maximals->tail()))) {

    // look for a negative literal of maximal weight
    for(int li=((int)eligible)-1; li>=0; li--) {
      Literal* lit=(*c)[li];
      if(isNegativeForSelection(lit)) {
        if (!singleSel || singleSel->weight() < lit->weight()) {
          singleSel = lit;
        }
      }
    }
  }

  // sel always initialised below
  LiteralList* sel;
  if(singleSel) {
    LiteralList::destroy(maximals);
    sel = LiteralList::empty();
    LiteralList::push(singleSel,sel);
  } else if (maximals) {
    sel = maximals;
  } else {
    sel = getMaximalsInOrder(c,eligible);
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

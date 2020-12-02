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
 * @file ELiteralSelector.cpp
 * Implements class ELiteralSelector.
 */

#include <algorithm>

#include "Lib/List.hpp"

#include "Term.hpp"
#include "Clause.hpp"

#include "ELiteralSelector.hpp"

using namespace std;
using namespace Lib;
using namespace Kernel;

LiteralList* ELiteralSelector::getMaximalsInOrder(Clause* c, unsigned eligible)
{
  CALL("ELiteralSelector::getMaximalsInOrder");

  LiteralList* res = LiteralList::empty();

  for(int li=((int)eligible)-1; li>=0; li--) {
    LiteralList::push((*c)[li],res);
  }

  _ord.removeNonMaximal(res);

  return res;
}

unsigned ELiteralSelector::lit_standard_diff(Literal* lit)
{
  CALL("ELiteralSelector::lit_standard_diff");

  if (lit->isEquality()) {
    unsigned w0 = lit->nthArgument(0)->weight();
    unsigned w1 = lit->nthArgument(1)->weight();
    return max(w0,w1)-min(w0,w1);
  } else {
    return lit->weight() - 1;
  }
}

/**
 * There is a similar macro in the code of E
 * called by the selections below.
 */
unsigned ELiteralSelector::lit_sel_diff_weight(Literal* lit)
{
  CALL("ELiteralSelector::lit_sel_diff_weight");

  return 100*lit_standard_diff(lit)+lit->weight();
}

void ELiteralSelector::doSelection(Clause* c, unsigned eligible)
{
  CALL("ELiteralSelector::doSelection");

  Literal* singleSel = nullptr;
  LiteralList* sel = LiteralList::empty();

  switch (_value) {
    case SelectNegativeLiterals: {
      for(int li=((int)eligible)-1; li>=0; li--) {
        Literal* lit=(*c)[li];
        if(isNegativeForSelection(lit)) {
          LiteralList::push(lit,sel);
        }
      }
      break;
    }
    case SelectPureVarNegLiterals: {
      for(int li=((int)eligible)-1; li>=0; li--) {
        Literal* lit=(*c)[li];
        if(isNegativeForSelection(lit) && lit->isTwoVarEquality()) {
          singleSel = lit;
          break;
        }
      }
      break;
    }
    case SelectSmallestNegLit: {
      for(int li=((int)eligible)-1; li>=0; li--) {
        Literal* lit=(*c)[li];
        if(isNegativeForSelection(lit)) {
          if (!singleSel || singleSel->weight() > lit->weight()) {
            singleSel = lit;
          }
        }
      }
      break;
    }
    case SelectDiffNegLit: {
      unsigned bestVal = 0;
      for(int li=((int)eligible)-1; li>=0; li--) {
        Literal* lit=(*c)[li];
        if(isNegativeForSelection(lit)) {
          unsigned val = lit_sel_diff_weight(lit);
          if (!singleSel || val > bestVal) {
            singleSel = lit;
            bestVal = val;
          }
        }
      }
      break;
    }
    case SelectGroundNegLit: {
      unsigned bestVal = 0;
      for(int li=((int)eligible)-1; li>=0; li--) {
        Literal* lit=(*c)[li];
        if(isNegativeForSelection(lit) && lit->ground()) {
          unsigned val = lit_sel_diff_weight(lit);
          if (!singleSel || val > bestVal) {
            singleSel = lit;
            bestVal = val;
          }
        }
      }
      break;
    }
    case SelectOptimalLit: {
      unsigned bestVal = 0;
      bool bestGround = false;
      for(int li=((int)eligible)-1; li>=0; li--) {
        Literal* lit=(*c)[li];
        if(isNegativeForSelection(lit) && (!bestGround || lit->ground())) {
          unsigned val = lit_sel_diff_weight(lit);
          if (!singleSel || (!bestGround && lit->ground()) || val > bestVal) {
            singleSel = lit;
            bestVal = val;
            bestGround = lit->ground();
          }
        }
      }
      break;
    }

  default:
    ASSERTION_VIOLATION;
  }

  if(singleSel) {
    LiteralList::destroy(sel);
    sel = LiteralList::empty();
    LiteralList::push(singleSel,sel);
  } else if (!sel) {
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

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
 * @file LiteralSelector.cpp
 * Implements class LiteralSelector for literal selection
 */

#include "Lib/Environment.hpp"
#include "Lib/Exception.hpp"

#include "Shell/Options.hpp"

#include "Clause.hpp"
#include "Signature.hpp"
#include "Term.hpp"
#include "LiteralSelectorOptions.hpp"

#undef LOGGING
#define LOGGING 0

namespace Kernel
{

using namespace std;

/**
 * Return true if literal @b l is positive for the purpose of
 * literal selection
 *
 * This function is to allow for easy implementation of
 * selection functions with negative numbers. Those functions
 * consider all literals except for equality to be of
 * opposite polarity.
 */
bool LiteralSelector::isPositiveForSelection(Literal* l) const
{
  if(l->isEquality()) {
    return l->isPositive(); //we don't change polarity for equality
  }
  return l->isPositive() ^ _reversePolarity;
}

/**
 * The selection will be performed among the literals with the
 * highest selection priority in the clause
 */
int LiteralSelector::getSelectionPriority(Literal* l) const
{
  Signature::Symbol* psym=env.signature->getPredicate(l->functor());
  if(psym->label() || psym->answerPredicate()) {
    return -2;
  }
  return 0;
}

/**
 * Return a literal selector object corresponding to number @b num
 *
 * It is expected that this function will be called at most once in
 * the run of Vampre process (see @b _instCtr documentation).
 *
 * The supported literal selector numbers should correspond to numbers
 * allowed in @b Shell::Options::setSelection.
 */
LiteralSelector* LiteralSelector::getSelector(const Ordering& ordering, const Options& options, int selectorNumber)
{
  int absNum = abs(selectorNumber);

  // LiteralSelector* res;
  auto resOpt = LiteralSelectors::OptionValues::find([&](auto token) -> Option<LiteralSelector*> {
      using OptionValue = TypeList::TokenType<decltype(token)>;
      using OptLiteralSelector = typename OptionValue::Type;
      if (OptionValue::number == absNum) {
        return Option<LiteralSelector*>(new OptLiteralSelector(ordering, options));
      } else {
        return {};
      }
  });
  if (resOpt.isNone()) {
    INVALID_OPERATION("Undefined selection function");
  }
  auto res = *resOpt;
  if(selectorNumber<0) {
    res->setReversePolarity(true);
  }
  return res;
}

/**
 * If there is a colored literal among the first @b eligible
 * ones, ensure at least one colored literal is selected
 */
void LiteralSelector::ensureSomeColoredSelected(Clause* c, unsigned eligible)
{
  if(c->color()==COLOR_TRANSPARENT) {
    //if no literal is colored, do nothing
    return;
  }

  unsigned selCnt=c->numSelected();

  for(unsigned i=0;i<selCnt;i++) {
    if((*c)[i]->color()!=COLOR_TRANSPARENT) {
      return;
    }
  }

  for(unsigned i=selCnt;i<eligible;i++) {
    if((*c)[i]->color()!=COLOR_TRANSPARENT) {
      swap((*c)[selCnt], (*c)[i]);
      c->setSelected(selCnt+1);
      return;
    }
  }

  ASS(eligible < c->length() || //the colored literals are not among the eligible ones ...
      c->splits());             // .. unless the color comes from the propositional part
}

/**
 * Perform literal selection on clause @b c
 *
 * First the literals eligible for selection are determined through
 * the @b getSelectionPriority function, and then the function
 * @b doSelection is called if there is more than one eligible
 * literal.
 */
void LiteralSelector::select(Clause* c, unsigned eligibleInp)
{
  ASS_LE(eligibleInp, c->length());

  if(eligibleInp==0) {
    eligibleInp = c->length();
  }

  if(eligibleInp<=1) {
    c->setSelected(eligibleInp);
    return;
  }

  unsigned eligible=1;
  { /* we order the clause so that the literals with highest `getSelectionPriority` are in the front, and eligible is the number of literals with that selection priority */ 
    int maxPriority=getSelectionPriority((*c)[0]);
    bool modified=false;

    for (unsigned i = 1; i < eligibleInp; i++) {
      int priority = getSelectionPriority((*c)[i]);
      if (priority == maxPriority) {
        if (eligible != i) {
          swap((*c)[i], (*c)[eligible]);
          modified = true;
        }
        eligible++;
      } else if (priority > maxPriority) {
        maxPriority = priority;
        eligible = 1;
        swap((*c)[i], (*c)[0]);
        modified = true;
      }
    }
    ASS_LE(eligible,eligibleInp);
    if(modified) {
      c->notifyLiteralReorder();
    }
  }

  if(eligible==1) {
    c->setSelected(eligible);
    return;
  }

  ASS_G(eligible,1);
  doSelection(c, eligible);
}

/**
 * Select all eligible literals in clause @b c
 */
void TotalLiteralSelector::doSelection(Clause* c, unsigned eligible)
{
  c->setSelected(eligible);
}

}

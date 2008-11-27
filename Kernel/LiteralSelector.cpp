/**
 * @file LiteralSelection.cpp
 * Implements class LiteralSelection for literal selection
 */

#include <algorithm>

#include "Term.hpp"
#include "Clause.hpp"

#include "LiteralSelector.hpp"

using namespace Kernel;

void EagerLiteralSelector::select(Clause* c)
{
  CALL("EagerLiteralSelector::select");

  c->setSelected(c->length());
}

void LightestNegativeLiteralSelection::select(Clause* c)
{
  CALL("LightestNegativeLiteralSelection::select");

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
    c->setSelected(clen);
  }

  c->setSelected(c->length());
}

void HeaviestNegativeLiteralSelection::select(Clause* c)
{
  CALL("LightestNegativeLiteralSelection::select");

  unsigned seli;
  //we assume, that weight of a literal is always greater than zero
  unsigned selWeight=0;
  unsigned clen=c->length();

  for(unsigned i=0;i<clen;i++) {
    if((*c)[i]->isNegative() && (*c)[i]->weight()>selWeight) {
      seli=i;
      selWeight=(*c)[i]->weight();
    }
  }

  if(selWeight) {
    std::swap((*c)[0], (*c)[seli]);
    c->setSelected(1);
  } else {
    c->setSelected(clen);
  }

  c->setSelected(c->length());
}


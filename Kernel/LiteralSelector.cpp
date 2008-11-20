/**
 * @file LiteralSelection.cpp
 * Implements class LiteralSelection for literal selection
 */

#include "Clause.hpp"

#include "LiteralSelector.hpp"

using namespace Kernel;

void EagerLiteralSelector::select(Clause* c)
{
  CALL("EagerLiteralSelector::select");

  c->setSelected(c->length());
}


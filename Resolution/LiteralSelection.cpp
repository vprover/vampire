/**
 * @file LiteralSelection.cpp
 * Implements class LiteralSelection for literal selection
 * @since 05/01/2008 Torrevieja
 */

#include "../Kernel/Term.hpp"
#include "../Kernel/Clause.hpp"

#include "LiteralSelection.hpp"

using namespace Resolution;

void LiteralSelection::select(Clause* c)
{
  CALL("LiteralSelection::select");

  c->setSelected(c->length());
} // LiteralSelection::select


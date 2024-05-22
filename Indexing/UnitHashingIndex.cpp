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
 * @file UnitHashingIndex.cpp
 * Implements class UnitHashingIndex.
 */

#include "UnitHashingIndex.hpp"

namespace Indexing
{

void UnitHashingIndex::handleClause(Clause* c, bool adding)
{
  if (c->length() != 1) {
    return;
  }
  Literal* lit = (*c)[0];
  if (lit->functor() > 0) { // we skip equational literals (let the standard subsuption do its job for them, if needed, they are likely non-ground)
    if (adding) {
      // we should not be getting the same unit twice
      // but with SaturationAlgorithm::addInputSOSClause, we skip forward reductions, so it's actually possible to insert twice
      _lookup.insert(lit,c);
    }
    else {
      _lookup.remove(lit);
    }
  }
}

Clause* UnitHashingIndex::getUnitLikeThis(Clause* c, bool opposite)
{
  Clause* res = 0;
  if (c->length() == 1) {
    Literal* lit = (*c)[0];
    if (lit->functor() > 0) {
      _lookup.find(opposite ? Literal::complementaryLiteral(lit) : lit,res);
    }
  }
  return res;
}

}

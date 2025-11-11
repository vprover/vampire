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
 * @file DelayedClauseIndex.cpp
 * Implements class DelayedClauseIndex.
 */

#include "DelayedClauseIndex.hpp"

#include "Kernel/EqHelper.hpp"

namespace Indexing {

void DelayedClauseIndex::handle(Clause* cl, Literal* lit, bool adding)
{
  ASS(lit->isPositive()); // we only have to index positive literals

  // SubtermIndex
  for (TypedTermList tt : iterTraits(EqHelper::getSubtermIterator(lit, _ord))) {
    if (tt.isTerm()) {
      tt = Term::linearize(tt.term());
    }
    _subtermIS.handle(TermLiteralClause{ tt, lit, cl }, adding);
  }

  if (lit->isEquality()) {
    // PositiveEqualitySideIndex
    for (unsigned i = 0; i < 2; i++) {
      TypedTermList tt(lit->termArg(i), SortHelper::getEqualityArgumentSort(lit));
      if (tt.isTerm()) {
        tt = Term::linearize(tt.term());
      }
      _posEqSideIS.handle(TermLiteralClause{ tt, lit, cl }, adding);
    }
  } else {
    // PositiveLiteralIndex
    _posLitIS.handle(LiteralClause{ Literal::linearize(lit), cl }, adding);

    // PredicateIndex
    DHSet<Clause*>* ptr;
    _predIS.getValuePtr(lit->functor(), ptr);
    if (adding) {
      ptr->insert(cl);
    } else {
      ASS(ptr);
      ptr->remove(cl);
    }
  }
}

} // namespace Indexing

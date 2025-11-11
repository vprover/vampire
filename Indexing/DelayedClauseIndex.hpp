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
 * @file DelayedClauseIndex.hpp
 * Defines class DelayedClauseIndex.
 */


#ifndef __DelayedClauseIndex__
#define __DelayedClauseIndex__

#include "Indexing/TermSubstitutionTree.hpp"
#include "Indexing/LiteralSubstitutionTree.hpp"

namespace Indexing {

class DelayedClauseIndex
{
  void handle(Clause* cl, Literal* lit, bool adding);

private:
  Ordering& _ord;
  const Options& _opt;

  TermSubstitutionTree<TermLiteralClause> _subtermIS;
  TermSubstitutionTree<TermLiteralClause> _posEqSideIS;
  LiteralSubstitutionTree<LiteralClause> _posLitIS;
  DHMap<unsigned, DHSet<Clause*>> _predIS;
};

} // namespace Indexing
#endif /* __TermIndex__ */

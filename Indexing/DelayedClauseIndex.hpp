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
public:
  void attach(SaturationAlgorithm* salg);

  bool checkReachableOrInsert(Clause* cl);
  void remove(Clause* cl);
  ClauseStack maybeUndelayClauses(Clause* cl);

  const DHMap<Clause*,unsigned>& clauses() const { return _clauses; }

private:
  bool checkReachable(Literal* lit);
  void handle(Clause* cl, Literal* lit, bool adding);

  const Ordering* _ord;
  const Options* _opt;

  DHMap<Clause*,unsigned> _clauses;

  TermSubstitutionTree<TermLiteralClause> _subtermIS;
  TermSubstitutionTree<TermLiteralClause> _posEqSideIS;
  LiteralSubstitutionTree<LiteralClause> _posLitIS;
  DHMap<unsigned, DHMap<Clause*,Literal*>> _predIS;

  TermIndex<TermLiteralClause>* _goalSubtermIndex;
  TermIndex<TermLiteralClause>* _goalLHSIndex;
  LiteralIndex<LiteralClause>* _goalLiteralIndex;
  GoalDirectedPredicateIndex* _goalPredicateIndex;
};

} // namespace Indexing
#endif /* __TermIndex__ */

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
 * @file GoalReachabilityHandler.hpp
 * Defines class GoalReachabilityHandler.
 */


#ifndef __GoalReachabilityHandler__
#define __GoalReachabilityHandler__

#include "Forwards.hpp"

#include "Indexing/TermSubstitutionTree.hpp"
#include "Saturation/SaturationAlgorithm.hpp"

#include <deque>

using namespace Kernel;
using namespace Indexing;

namespace Shell {

class GoalReachabilityHandler {
public:
  GoalReachabilityHandler(SaturationAlgorithm& salg);

  void addClause(Clause* cl);
  void removeClause(Clause* cl);
  [[nodiscard]] bool iterate(ClauseStack& newGoalClauses);

private:
  void handleGoalClause(Clause* cl, bool adding);
  void handleNonGoalTerm(Clause* cl, TypedTermList t, bool adding);
  void updateWatchedLiteral(Clause* cl);

  [[nodiscard]] bool baseInference(Clause* cl, TermList t, Literal* lit, ResultSubstitution& unif, bool tIsResult);
  [[nodiscard]] bool base2Inference(Clause* cl, TermList t, Literal* lit, ResultSubstitution& unif, bool tIsResult);
  void chain1Inference(Clause* cl, TermList t, Literal* lit, ResultSubstitution& unif, bool tIsResult);
  void chain2Inference(Clause* cl, TermList t, TermList lhs, Literal* lit, ResultSubstitution& unif, bool lhsIsResult);

  friend class GoalNonLinearityHandler;

  std::deque<Clause*> _todoNonGoalClauses;
  std::deque<Clause*> _todoGoalClauses;

  struct NonGoalClauseInfo {
    unsigned watchedIndex = 0;
    std::deque<TypedTermList> unprocessed;
    Stack<TypedTermList> processed; // these are saved so we can remove them from indices
    DHSet<TypedTermList> seen;
  };
  DHMap<Clause*, NonGoalClauseInfo> _nonGoalClauses;

  TermSubstitutionTree<TermWithValue<TermLiteralClause>> _baseForwardIndex;
  TermSubstitutionTree<TermWithValue<TermLiteralClause>> _chain1ForwardIndex;
  TermSubstitutionTree<TermWithValue<TermLiteralClause>> _chain2ForwardIndex;

  TermSubstitutionTree<TermWithValue<std::pair<TypedTermList, Clause*>>> _backwardSubtermIndex;
  TermSubstitutionTree<TermWithValue<Clause*>> _backwardTermIndex;

  const Ordering& _ord;
  const Options& _opt;
  const unsigned _chainLimit;
};

}

#endif

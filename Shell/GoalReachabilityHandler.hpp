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

using namespace Kernel;
using namespace Indexing;

namespace Shell {

class GoalReachabilityHandler {
public:
  GoalReachabilityHandler(SaturationAlgorithm& salg);

  void addClause(Clause* cl);
  void removeClause(Clause* cl);
  [[nodiscard]] bool iterate();

  ClauseStack goalClauses() {
    ClauseStack res;
    std::swap(res, _newGoalClauses);
    return res;
  }

private:
  void handleGoalClause(Clause* cl, bool adding);
  void handleNonGoalTerm(Clause* cl, TypedTermList t, bool adding);
  bool updateWatchedLiteral(Clause* cl);

  bool baseInference(Clause* cl, TermList t, Literal* lit, ResultSubstitution& unif, bool tIsResult);
  bool base2Inference(Clause* cl, TermList t, Literal* lit, ResultSubstitution& unif, bool tIsResult);
  void chain1Inference(Clause* cl, TermList t, Literal* lit, ResultSubstitution& unif, bool tIsResult);
  void chain2Inference(Clause* cl, TermList t, TermList lhs, Literal* lit, ResultSubstitution& unif, bool lhsIsResult);

  friend class GoalNonLinearityHandler;

  Deque<Clause*> _todoNonGoalClauses;
  Deque<Clause*> _todoGoalClauses;

  struct NonGoalClauseInfo {
    unsigned watchedIndex = 0;
    Stack<TypedTermList> unprocessed;
    Stack<TypedTermList> processed; // these are saved so we can remove them from indices
  };
  DHMap<Clause*, NonGoalClauseInfo> _nonGoalClauses;

  TermSubstitutionTree<TermWithValue<TermLiteralClause>> _baseForwardIndex;
  TermSubstitutionTree<TermWithValue<TermLiteralClause>> _chain1ForwardIndex;
  TermSubstitutionTree<TermWithValue<TermLiteralClause>> _chain2ForwardIndex;

  TermSubstitutionTree<TermWithValue<std::pair<TypedTermList, Clause*>>> _backwardSubtermIndex;
  TermSubstitutionTree<TermWithValue<Clause*>> _backwardTermIndex;

  ClauseStack _newGoalClauses;

  const Ordering& _ord;
  const Options& _opt;
  const unsigned _chainLimit;
};

}

#endif

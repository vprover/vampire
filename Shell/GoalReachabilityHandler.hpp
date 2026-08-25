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

using LinearityConstraint = std::pair<TypedTermList,TypedTermList>;
using LinearityConstraints = Stack<LinearityConstraint>;

using ClauseTermPair = std::pair<Clause*, Term*>;
using ClauseTermPairs = Stack<ClauseTermPair>;

struct Chain {
  Chain(TypedTermList origLhs, TypedTermList lhs, TypedTermList rhs, unsigned length, bool isBase);

  friend std::ostream& operator<<(std::ostream& out, Chain const& self)
  {
    out << self.lhs.untyped();
    if (self.rhs.isNonEmpty()) {
      out << " -> " << self.rhs.untyped();
    }
    out << " (length " << self.length << ")";
    return out;
  }

  TypedTermList origLhs;
  TypedTermList lhs;
  TypedTermList rhs;
  unsigned length;
  bool isBase;

  TypedTermList linearLhs;
  LinearityConstraints constraints;

  bool processed = false;
  bool expanded = false;
  Clause* origin = nullptr;
};

template<typename T>
struct ItemChain
{
  T item;
  Chain* chain;

  T const& key() const { return item; }
  auto asTuple() const { return std::make_tuple(chain, item); }

  IMPL_COMPARISONS_FROM_TUPLE(ItemChain)

  friend std::ostream& operator<<(std::ostream& out, ItemChain const& self) { return out; }
};

using TermChain = ItemChain<TypedTermList>;
using LiteralChain = ItemChain<Literal*>;

// class GoalNonLinearityHandler {
// public:
//   GoalNonLinearityHandler(SaturationAlgorithm& salg, GoalReachabilityHandler& handler);

//   [[nodiscard]] ClauseTermPairs get(Clause* ngcl, TypedTermList goalTerm, TypedTermList nonGoalTerm,
//     const LinearityConstraints& cons, ResultSubstitution& subst, bool goalIsResult);

//   void addNonGoalClause(Clause* cl);
//   void handleChain(Chain* chain, bool insert);

// private:
//   void perform(Clause* ngcl, TypedTermList goalTerm, TypedTermList nonGoalTerm,
//     const LinearityConstraints& cons, ResultSubstitution& subst, bool goalIsResult);

//   const Ordering& ord;
//   GoalReachabilityHandler& handler;

//   TermSubstitutionTree<TermChain> _nonLinearGoalTermIndex;
//   TermSubstitutionTree<TermChain> _nonLinearGoalLHSIndex;
//   LiteralSubstitutionTree<LiteralChain> _nonLinearGoalLiteralIndex;

//   std::shared_ptr<SuperpositionLHSIndex> _lhsIndex;
//   std::shared_ptr<SuperpositionSubtermIndex<false>> _subtermIndex;
//   std::shared_ptr<BinaryResolutionIndex> _resolutionIndex;
// };

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
  void updateWatchedLiteral(Clause* cl);

  friend class GoalNonLinearityHandler;

  Deque<std::pair<Clause*, TypedTermList>> _todo;
  DHMap<Clause*, unsigned> _nonGoalWatchedLiterals;

  TermSubstitutionTree<TermLiteralClause> _baseForwardIndex;
  TermSubstitutionTree<TermLiteralClause> _chain1ForwardIndex;
  TermSubstitutionTree<TermLiteralClause> _chain2ForwardIndex;

  ClauseStack _newGoalClauses;
  // ClauseTermPairs _newSuperposableTerms;

  // Deque<Chain*> _newChainsToHandle;

  const Ordering& _ord;
  const Options& _opt;
  const unsigned _chainLimit;

  // stores which chains belong to which goal clause
  // DHMap<Clause*, Stack<Chain*>> _chainMap;
  // // index for chain LHS subterms unifying with non-goal RHSs
  // TermSubstitutionTree<TermChain> _linearChainSubtermIndex;
  // // index for chain LHS subterms unifying with chain RHSs
  // TermSubstitutionTree<TermChain> _nonlinearChainSubtermIndex;
  // // index for chain RHSs unifying with chain LHS subterms
  // TermSubstitutionTree<TermChain> _chainRHSIndex;

  // // stores which terms are superposable in which non-goal clause
  // DHMap<Clause*, DHSet<Term*>> _superposableTerms;
  // // index for non-goal RHSs
  // TermSubstitutionTree<TermLiteralClause> _nonGoalRHSIndex;

  // GoalNonLinearityHandler _nonLinearityHandler;
};

}

#endif

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

#include "Indexing/TermIndex.hpp"
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
  Chain(TypedTermList lhs, TypedTermList rhs, unsigned length, bool isBase);

  friend std::ostream& operator<<(std::ostream& out, Chain const& self)
  {
    out << self.lhs.untyped();
    if (self.rhs.isNonEmpty()) {
      out << " -> " << self.rhs.untyped();
    }
    out << " (length " << self.length << ")";
    return out;
  }

  TypedTermList lhs;
  TypedTermList rhs;
  unsigned length;
  bool isBase;

  TypedTermList linearLhs;
  LinearityConstraints constraints;
};

struct TermChain
{
  TypedTermList term;
  Chain* chain;

  TypedTermList const& key() const { return term; }
  auto asTuple() const { return std::make_tuple(chain, term); }

  IMPL_COMPARISONS_FROM_TUPLE(TermChain)

  friend std::ostream& operator<<(std::ostream& out, TermChain const& self) { return out; }
};

class GoalNonLinearityHandler {
public:
  GoalNonLinearityHandler(SaturationAlgorithm& salg, GoalReachabilityHandler& handler);

  [[nodiscard]] static ClauseTermPairs get(Clause* ngcl, TypedTermList goalTerm, TypedTermList nonGoalTerm, const LinearityConstraints& cons);

  void addNonGoalClause(Clause* cl);
  void addChain(Chain* chain);
  void removeGoalClause(Clause* cl) { NOT_IMPLEMENTED; }

  // TODO implement removal
  void removeClause(Clause* cl) { NOT_IMPLEMENTED; }

private:
  void perform(Clause* ngcl, TypedTermList goalTerm, TypedTermList nonGoalTerm, const LinearityConstraints& cons);

  const Ordering& ord;
  GoalReachabilityHandler& handler;

  TermSubstitutionTree<TermChain> _nonLinearGoalTermIndex;
  TermSubstitutionTree<TermChain> _nonLinearGoalLHSIndex;

  std::shared_ptr<SuperpositionLHSIndex> _lhsIndex;
  std::shared_ptr<SuperpositionSubtermIndex> _subtermIndex;
};

/**
 * We maintain
 * - a set of "chains", pairs of terms (s, t), s.t. given non-goal clause l ≈ r v C where l ≈ r is selected,
 *   if r unifies with some strict subterm r' of s with substitution θ
 */

class GoalReachabilityHandler {
public:
  GoalReachabilityHandler(SaturationAlgorithm& salg) : ord(salg.getOrdering()), _nonLinearityHandler(salg, *this) {}

  void addClause(Clause* cl);
  void removeClause(Clause* cl) { NOT_IMPLEMENTED; }

  [[nodiscard]] bool isTermSuperposable(Clause* cl, TypedTermList t) const;
  const ClauseStack& goalClauses() { return _newGoalClauses; }
  const ClauseTermPairs& superposableTerms() { return _newSuperposableTerms; }

private:
  [[nodiscard]] bool tryAddNonGoalClause(Clause* cl);
  void addGoalClause(Clause* cl);
  void handleNewChains();

  [[nodiscard]] bool isReached(Clause* ngCl, TypedTermList ngRhs, TypedTermList gSubterm,
    const Chain* chain, ResultSubstitution& subst, bool result);

  [[nodiscard]] Stack<Chain*> buildNewChains(Chain* chain);

  void handleNonGoalClause(Clause* cl, bool insert);

  void addSuperposableTerm(Clause* ngcl, Term* t);

  friend class GoalNonLinearityHandler;

  const Ordering& ord;

  // index for chain LHS subterms unifying with non-goal RHSs
  TermSubstitutionTree<TermChain> _linearChainSubtermIndex;
  // index for chain LHS subterms unifying with chain RHSs
  TermSubstitutionTree<TermChain> _nonlinearChainSubtermIndex;
  // index for chain RHSs unifying with chain LHS subterms
  TermSubstitutionTree<TermChain> _chainRHSIndex;

  // index for non-goal RHSs
  TermSubstitutionTree<TermLiteralClause> _nonGoalRHSIndex;

  ClauseStack _newGoalClauses;

  ClauseTermPairs _newSuperposableTerms;
  DHMap<Clause*, DHSet<Term*>> _superposableTerms;

  GoalNonLinearityHandler _nonLinearityHandler;

  Stack<Chain*> _newChainsToHandle;
};

}

#endif
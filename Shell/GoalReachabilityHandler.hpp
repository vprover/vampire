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

using namespace Kernel;
using namespace Indexing;

namespace Shell {

struct TermTermLiteralClause
{
  TypedTermList term;
  TypedTermList side;
  Literal* literal = nullptr;
  Clause* clause = nullptr;

  TypedTermList const& key() const { return term; }

  auto asTuple() const
  { return std::make_tuple(clause->number(), literal->getId(), side, term); }

  IMPL_COMPARISONS_FROM_TUPLE(TermTermLiteralClause)

  friend std::ostream& operator<<(std::ostream& out, TermTermLiteralClause const& self)
  { return out << "(" << self.term << ", " << self.side << ", " << *self.literal << ", " << *self.clause << ")"; }
};

struct TermClause 
{
  TypedTermList term;
  Clause* clause = nullptr;

  TypedTermList const& key() const { return term; }

  auto asTuple() const
  { return std::make_tuple(clause->number(), term); }

  IMPL_COMPARISONS_FROM_TUPLE(TermClause)

  friend std::ostream& operator<<(std::ostream& out, TermClause const& self)
  { return out << "(" << self.term << ", " << *self.clause << ")"; }
};

using LinearityConstraint = std::pair<TypedTermList,TypedTermList>;
using LinearityConstraints = Stack<LinearityConstraint>;

struct LinearTermLiteralClause
{
  TypedTermList term;
  LinearityConstraints constraints;
  Literal* literal = nullptr;
  Clause* clause = nullptr;

  TypedTermList const& key() const { return term; }

  auto  asTuple() const
  { return std::make_tuple(clause->number(), constraints, literal->getId(), term); }

  IMPL_COMPARISONS_FROM_TUPLE(LinearTermLiteralClause)

  friend std::ostream& operator<<(std::ostream& out, LinearTermLiteralClause const& self)
  { return out << "("
               << self.term << ", "
               << self.constraints << ", "
               << self.literal << ", "
               << Output::ptr(self.clause)
               << ")"; }
};

using ClauseTermPair = std::pair<Clause*, TypedTermList>;
using ClauseTermPairs = Stack<ClauseTermPair>;

class GoalNonLinearityHandler {
public:
  GoalNonLinearityHandler(const Ordering& ord, const GoalReachabilityHandler& handler) : ord(ord), handler(handler) {}

  [[nodiscard]] ClauseTermPairs checkNonGoalClause(Clause* cl);
  [[nodiscard]] ClauseTermPairs checkGoalClause(Clause* cl);

  // TODO implement removal
  void removeClause(Clause* cl) { NOT_IMPLEMENTED; }

private:
  void perform(Clause* ngcl, const LinearityConstraints& cons, ResultSubstitution* subst, bool result, ClauseTermPairs& res);

  const Ordering& ord;
  const GoalReachabilityHandler& handler;

  TermSubstitutionTree<LinearTermLiteralClause> _nonLinearGoalTermIndex;
  TermSubstitutionTree<LinearTermLiteralClause> _nonLinearGoalLHSIndex;

  TermSubstitutionTree<TermLiteralClause> _nonGoalLHSIndex;
  TermSubstitutionTree<TermLiteralClause> _nonGoalSubtermIndex;
};

class GoalReachabilityHandler {
public:
  GoalReachabilityHandler(const Ordering& ord) : ord(ord), _nonLinearityHandler(ord, *this) {}

  // returns clauses that become goal clauses when adding this clause
  // note that the clause itself can be among them
  [[nodiscard]] std::pair<ClauseStack, ClauseTermPairs> addClause(Clause* cl);
  void removeClause(Clause* cl) { NOT_IMPLEMENTED; }

private:
  [[nodiscard]] std::pair<ClauseStack, ClauseTermPairs> addGoalClause(Clause* cl);

  struct ReachabilityTree {
    ReachabilityTree(GoalReachabilityHandler& handler, Clause* cl) : handler(handler), cl(cl) {}

    // Take smaller side(s) and explore all possible unifiers
    // with strict subterms of LHSs of goal clauses. If we find any
    // unifier σ and goal clause l ≈ r \lor C such that rσ = r,
    // then the clause we are considering is a goal clause, otherwise
    // we repeat the process with rσ.
    // Returns true iff the term could be inserted, i.e. the term has no goal
    // term instances yet.
    [[nodiscard]] bool addTerm(TypedTermList t);
    // Returns true iff the term could be inserted, i.e. the term has no goal
    // term instances yet.
    [[nodiscard]] static bool canBeAdded(TypedTermList t, ResultSubstitution& subst, bool result);

    // TODO store terms that have been superposed into by non-goal terms
    DHSet<TypedTermList> terms;
    GoalReachabilityHandler& handler;
    DHSet<TypedTermList> nonGoalSuperposableTerms;
    Clause* cl;
  };

  friend class GoalNonLinearityHandler;

  DHMap<Clause*, ReachabilityTree*> clauseTrees;
  const Ordering& ord;

  TermSubstitutionTree<TermTermLiteralClause> _goalSubtermIndex;
  TermSubstitutionTree<TermClause> _rhsIndex;

  GoalNonLinearityHandler _nonLinearityHandler;
};

}

#endif
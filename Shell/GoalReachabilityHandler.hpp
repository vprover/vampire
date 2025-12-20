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
  GoalNonLinearityHandler(const Ordering& ord, GoalReachabilityHandler& handler) : ord(ord), handler(handler) {}

  [[nodiscard]] ClauseTermPairs addNonGoalClause(Clause* cl);
  [[nodiscard]] ClauseTermPairs addGoalClause(Clause* cl);
  void removeNonGoalClause(Clause* cl);
  void removeGoalClause(Clause* cl) { NOT_IMPLEMENTED; }

  // TODO implement removal
  void removeClause(Clause* cl) { NOT_IMPLEMENTED; }

private:
  void perform(Clause* ngcl, TypedTermList goalTerm, TypedTermList nonGoalTerm, const LinearityConstraints& cons, ClauseTermPairs& res);

  const Ordering& ord;
  GoalReachabilityHandler& handler;

  TermSubstitutionTree<LinearTermLiteralClause> _nonLinearGoalTermIndex;
  TermSubstitutionTree<LinearTermLiteralClause> _nonLinearGoalLHSIndex;

  TermSubstitutionTree<TermLiteralClause> _nonGoalLHSIndex;
  TermSubstitutionTree<TermLiteralClause> _nonGoalSubtermIndex;
};

struct Chain {
  Chain(TypedTermList lhs, TypedTermList rhs, unsigned length);

  bool isBase() const { return rhs.isEmpty(); }
  bool isLengthZero() const { return length==0; }
  bool isLengthOne() const { return length==1; }

  friend std::ostream& operator<<(std::ostream& out, Chain const& self)
  {
    out << self.lhs;
    if (!self.isBase()) {
      out << " -> " << self.rhs;
    }
    out << " (" << self.length << ")";
    return out;
  }

  TypedTermList lhs;
  TypedTermList rhs;
  unsigned length;

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

/**
 * We maintain
 * - a set of "chains", pairs of terms (s, t), s.t. given non-goal clause l ≈ r v C where l ≈ r is selected,
 *   if r unifies with some strict subterm r' of s with substitution θ
 */

class GoalReachabilityHandler {
public:
  GoalReachabilityHandler(const Ordering& ord) : ord(ord), _nonLinearityHandler(ord, *this) {}

  // returns clauses that become goal clauses when adding this clause
  // note that the clause itself can be among them
  [[nodiscard]] std::pair<ClauseStack, ClauseTermPairs> addClause(Clause* cl);
  void removeClause(Clause* cl) { NOT_IMPLEMENTED; }
  [[nodiscard]] bool isTermSuperposable(Clause* cl, TypedTermList t) const;

  [[nodiscard]] std::pair<ClauseStack, ClauseTermPairs> iterate(Clause* cl);
  [[nodiscard]] bool addNonGoalClause(Clause* cl);

private:
  [[nodiscard]] std::pair<ClauseStack, ClauseTermPairs> addGoalClause(Clause* cl);

  void addChain(Chain* chain);
  [[nodiscard]] std::pair<ClauseStack, ClauseTermPairs> checkNonGoalReachability(Chain* chain);
  [[nodiscard]] Stack<Chain*> buildNewChains(Chain* chain);

  [[nodiscard]] Stack<Chain*> insertGoalClause(Clause* cl);
  void handleNonGoalClause(Clause* cl, bool insert);

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

  // index for chain LHS subterms unifying with non-goal RHSs
  TermSubstitutionTree<TermChain> _linearChainSubtermIndex;
  // index for chain LHS subterms unifying with chain RHSs
  TermSubstitutionTree<TermChain> _nonlinearChainSubtermIndex;
  // index for chain RHSs unifying with chain LHS subterms
  TermSubstitutionTree<TermChain> _chainRHSIndex;

  // index for non-goal RHSs
  TermSubstitutionTree<TermLiteralClause> _nonGoalRHSIndex;

  DHMap<Clause*, DHSet<Term*>> _superposableTerms;

  GoalNonLinearityHandler _nonLinearityHandler;
};

}

#endif
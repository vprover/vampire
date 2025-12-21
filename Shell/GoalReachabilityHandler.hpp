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

using ClauseTermPair = std::pair<Clause*, Term*>;
using ClauseTermPairs = Stack<ClauseTermPair>;

class GoalNonLinearityHandler {
public:
  GoalNonLinearityHandler(const Ordering& ord, GoalReachabilityHandler& handler) : ord(ord), handler(handler) {}

  [[nodiscard]] static ClauseTermPairs get(Clause* ngcl, TypedTermList goalTerm, TypedTermList nonGoalTerm, const LinearityConstraints& cons);

  void addNonGoalClause(Clause* cl);
  void addGoalClause(Clause* cl);
  void removeNonGoalClause(Clause* cl);
  void removeGoalClause(Clause* cl) { NOT_IMPLEMENTED; }

  // TODO implement removal
  void removeClause(Clause* cl) { NOT_IMPLEMENTED; }

private:
  void perform(Clause* ngcl, TypedTermList goalTerm, TypedTermList nonGoalTerm, const LinearityConstraints& cons);

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

private:
  [[nodiscard]] ClauseStack addGoalClause(Clause* cl);
  [[nodiscard]] bool addNonGoalClause(Clause* cl);

  [[nodiscard]] bool isReached(Clause* ngCl, TypedTermList ngRhs, TypedTermList gSubterm,
    const Chain* chain, ResultSubstitution& subst, bool result);

  void addChain(Chain* chain);
  [[nodiscard]] ClauseStack checkNonGoalReachability(Chain* chain);
  [[nodiscard]] Stack<Chain*> buildNewChains(Chain* chain);

  [[nodiscard]] Stack<Chain*> insertGoalClause(Clause* cl);
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

  ClauseTermPairs _newSuperposableTerms;
  DHMap<Clause*, DHSet<Term*>> _superposableTerms;

  GoalNonLinearityHandler _nonLinearityHandler;
};

}

#endif
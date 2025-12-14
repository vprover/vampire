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
  { return out << "(" << self.term << ", " << self.side << ", " << *self.literal << *self.clause << ")"; }
};

class GoalReachabilityHandler {
public:
  GoalReachabilityHandler(const Ordering& ord, const Options& opt) : ord(ord), opt(opt) {}

  // returns true if the clause is a goal clause
  bool addClause(Clause* cl); // TODO should return also the clauses that became goal
  void removeClause(Clause* cl);

private:
  void addGoalClause(Clause* cl);

  struct ReachabilityTree {
    ReachabilityTree(GoalReachabilityHandler& handler) : handler(handler) {}

    // Take smaller side(s) and explore all possible unifiers
    // with strict subterms of LHSs of goal clauses. If we find any
    // unifier σ and goal clause l ≈ r \lor C such that rσ = r,
    // then the clause we are considering is a goal clause, otherwise
    // we repeat the process with rσ.
    // Returns true iff the term could be inserted, i.e. the term has no goal
    // term instances yet.
    bool addTerm(TypedTermList t);
    // Returns true iff the term could be inserted, i.e. the term has no goal
    // term instances yet.
    bool canBeAdded(TypedTermList t, ResultSubstitution& subst, bool result);

    // TODO store terms that have been superposed into by non-goal terms
    DHSet<TypedTermList> terms;
    GoalReachabilityHandler& handler;
  };

  DHMap<Clause*, ReachabilityTree*> clauseTrees;
  const Ordering& ord;
  const Options& opt;

  TermSubstitutionTree<TermTermLiteralClause> _goalSubtermIndex;
  TermSubstitutionTree<TermLiteralClause> _rhsIndex;
};

}

#endif
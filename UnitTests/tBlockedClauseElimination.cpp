/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include <algorithm>
#include <initializer_list>
#include <string>
#include <vector>

#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"

#include "Lib/Environment.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Problem.hpp"

#include "Shell/BlockedClauseElimination.hpp"

using namespace Kernel;
using namespace Shell;

static Problem *problemFromClauses(std::initializer_list<Clause *> cls)
{
  UnitList *units = UnitList::empty();
  for (Clause *cl : cls) {
    UnitList::push(cl, units);
  }
  Problem *prb = new Problem(units);
  env.setMainProblem(prb);
  return prb;
}

/** the clauses' literals, sorted, so that a test does not depend on the elimination order */
static std::vector<std::string> runBCE(std::initializer_list<Clause *> cls, bool useSubsumption)
{
  Problem *prb = problemFromClauses(cls);
  BlockedClauseElimination bce(/*forceEquationally=*/false, useSubsumption);
  bce.apply(*prb);

  std::vector<std::string> res;
  for (const auto &u : iterTraits(UnitList::Iterator(prb->units()))) {
    res.push_back(u->asClause()->literalsOnlyToString());
  }
  std::sort(res.begin(), res.end());
  return res;
}

static bool contains(const std::vector<std::string> &cls, const std::string &lits)
{
  return std::find(cls.begin(), cls.end(), lits) != cls.end();
}

#define MY_SYNTAX_SUGAR \
  DECL_DEFAULT_VARS     \
  DECL_SORT(s)          \
  DECL_CONST(a, s)      \
  DECL_CONST(b, s)      \
  DECL_CONST(c, s)      \
  DECL_PRED(p, {s})     \
  DECL_PRED(q, {s})     \
  DECL_PRED(r, {s})     \
  DECL_PRED(t, {s})     \
  DECL_PRED(u, {s})

/* Note: the clause sets below are padded with "anchor" clauses giving every predicate both
 * polarities. Without them, a candidate literal whose predicate never occurs negated has no
 * resolution partners at all and its clause gets blocked vacuously, which drowns out the
 * property actually under test. */

TEST_FUN(subsumed_resolvent_blocks)
{
  MY_SYNTAX_SUGAR

  // {p(X) \/ q(X)} is blocked on p(X) only because its single resolvent,
  // {q(a) \/ r(a)}, while not a tautology, is subsumed by {q(a)}.
  auto cls = {clause({p(x), q(x)}),
              clause({~p(a), r(a)}),
              clause({q(a)}),
              clause({~q(y), t(y)}),
              clause({p(a), u(a)}),
              clause({~u(a)}),
              clause({~t(c)}),
              clause({~r(a)})};

  auto without = runBCE(cls, /*useSubsumption=*/false);
  ASS_EQ(without.size(), 8);
  ASS(contains(without, "p(X0) | q(X0)"));

  auto with = runBCE(cls, /*useSubsumption=*/true);
  ASS_EQ(with.size(), 7);
  ASS(!contains(with, "p(X0) | q(X0)"));
}

TEST_FUN(self_subsumption_excluded)
{
  MY_SYNTAX_SUGAR

  // {p(X) \/ q(Y)} has two resolution partners on p(X):
  //  - {~p(b) \/ r(c)} gives {q(Y) \/ r(c)}, subsumed by {q(V) \/ r(c)};
  //  - {~p(a) \/ p(b)}  gives {q(Y) \/ p(b)}, which is subsumed -- but only by the very
  //    clause we would be removing, so it does not count and the clause is not blocked.
  // Dropping the `premise != exclude` guard in subsumedBy makes this test fail.
  auto cls = {clause({p(x), q(y)}),
              clause({~p(a), p(b)}),
              clause({~p(b), r(c)}),
              clause({q(z), r(c)}),
              clause({p(a), t(a)}),
              clause({~t(a)}),
              clause({~q(c), u(c)}),
              clause({~u(c)}),
              clause({~r(c)})};

  auto with = runBCE(cls, /*useSubsumption=*/true);
  ASS_EQ(with.size(), 9);
  ASS(contains(with, "p(X0) | q(X1)"));
}

TEST_FUN(resolved_literal_dropped_from_partner)
{
  MY_SYNTAX_SUGAR

  // Reduced from Problems/SYN/SYN053+1.p, where -bce on -bces on used to answer
  // CounterSatisfiable for a theorem. Resolving {~p \/ ~p} against {p \/ q(X) \/ p \/ q(Y)}
  // must drop *both* copies of the resolved literal from the partner, not just the one at the
  // resolved position: leaving the second p behind pairs it with the second ~p and reports the
  // resolvent to be a tautology, blocking a clause that is not blocked. The right resolvent is
  // {q(X) \/ q(Y)}, which is neither a tautology nor subsumed here.
  auto cls = {clause({~p(a), ~p(a)}),
              clause({p(a), q(x), p(a), q(y)}),
              clause({~q(b), ~q(c)})};

  auto with = runBCE(cls, /*useSubsumption=*/true);
  ASS_EQ(with.size(), 3);
  ASS(contains(with, "~p(a) | ~p(a)"));
}

TEST_FUN(duplicates_and_tautologies_in_input)
{
  MY_SYNTAX_SUGAR

  // A clause with a duplicate literal, and a tautology, would both violate an invariant of
  // the multi-literal matching in ClauseCodeTree, so they are kept out of the index; the
  // blocking of {p(X) \/ q(X)} must still go through.
  auto cls = {clause({p(x), q(x)}),
              clause({~p(a), r(a)}),
              clause({q(a)}),
              clause({~q(y), t(y)}),
              clause({p(a), u(a)}),
              clause({~u(a)}),
              clause({~t(c)}),
              clause({~r(a)}),
              clause({t(b), t(b), ~u(b)}),
              clause({u(c), ~u(c), r(b)})};

  auto with = runBCE(cls, /*useSubsumption=*/true);
  ASS(!contains(with, "p(X0) | q(X0)"));
}

TEST_FUN(equational_path_unaffected)
{
  MY_SYNTAX_SUGAR

  // A positive equality atom in the problem forces the (weaker) equational tautologyhood
  // check, which does not work with an mgu and so has no resolvent to hand to the index.
  auto cls = {clause({p(x), q(x)}),
              clause({~p(a), r(a)}),
              clause({q(a)}),
              clause({~q(y), t(y)}),
              clause({p(a), u(a)}),
              clause({~u(a)}),
              clause({~t(c)}),
              clause({~r(a)}),
              clause({a == b})};

  auto with = runBCE(cls, /*useSubsumption=*/true);
  ASS(contains(with, "p(X0) | q(X0)"));
}

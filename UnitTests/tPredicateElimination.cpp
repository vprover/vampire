/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include <initializer_list>

#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"

#include "Lib/Environment.hpp"
#include "Shell/Statistics.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Problem.hpp"

#include "Shell/PredicateElimination.hpp"

using namespace Kernel;
using namespace Shell;

static Problem *problemFromClauses(std::initializer_list<Clause *> cls)
{
  UnitList *units = UnitList::empty();
  for (Clause *cl : cls) {
    UnitList::push(cl, units);
  }
  return new Problem(units);
}

static ClauseStack collectClauses(Problem &prb)
{
  ClauseStack res;
  for (const auto& u : iterTraits(UnitList::Iterator(prb.units()))) {
    res.push(u->asClause());
  }
  return res;
}

static bool containsPredicate(const ClauseStack &cls, unsigned pred)
{
  for (Clause *cl : cls) {
    for (unsigned i = 0; i < cl->length(); i++) {
      if ((*cl)[i]->functor() == pred) {
        return true;
      }
    }
  }
  return false;
}

/** the clause of the given length -- expected to exist and be unique */
static Clause *theClauseOfLength(const ClauseStack &cls, unsigned len)
{
  Clause *found = nullptr;
  for (Clause *cl : cls) {
    if (cl->length() == len) {
      ASS(!found);
      found = cl;
    }
  }
  ASS(found);
  return found;
}

static ClauseStack runPE(std::initializer_list<Clause *> cls,
                             bool forceEquationally = false,
                             float totalLimit = 2.0,
                             bool useSubsumption = false)
{
  Problem *prb = problemFromClauses(cls);
  PredicateElimination pe(forceEquationally, totalLimit, useSubsumption);
  pe.apply(*prb);
  return collectClauses(*prb);
}

/* Note: many tests below include the clause {q(y) \/ ~q(f(y))}, in which q is
 * "self-referential" and thus protected from elimination. Without such an anchor,
 * eliminating p typically leaves q occurring in one polarity only, whereupon
 * PE (correctly, but distractingly for the tests) deletes all the q-clauses too. */

#define MY_SYNTAX_SUGAR \
  DECL_DEFAULT_VARS     \
  DECL_SORT(s)          \
  DECL_CONST(a, s)      \
  DECL_CONST(b, s)      \
  DECL_CONST(c, s)      \
  DECL_FUNC(f, {s}, s)  \
  DECL_PRED(p, {s})     \
  DECL_PRED(q, {s})     \
  DECL_PRED(r, {s})

TEST_FUN(mgu_basic)
{
  MY_SYNTAX_SUGAR

  // {p(a)}, {~p(x) \/ q(x)} ---> {q(a)}
  auto res = runPE({clause({p(a)}), clause({~p(x), q(x)}),
                    clause({q(y), ~q(f(y))})});

  ASS_EQ(res.size(), 2);
  ASS(!containsPredicate(res, p.functor()));
  Clause *resolvent = theClauseOfLength(res, 1);
  ASS_EQ(resolvent->literalsOnlyToString(), "q(a)");
  ASS(resolvent->inference().rule() == InferenceRule::PREDICATE_ELIMINATION);
}

TEST_FUN(mgu_nonunifiable_pair_dropped)
{
  MY_SYNTAX_SUGAR

  // no equality in the problem: the pair does not unify, no resolvent
  auto res = runPE({clause({p(a)}), clause({~p(b), q(b)}),
                    clause({q(y), ~q(f(y))})});

  ASS_EQ(res.size(), 1); // just the q-anchor
  ASS(!containsPredicate(res, p.functor()));
}

TEST_FUN(mgu_empty_clause)
{
  MY_SYNTAX_SUGAR

  // {p(a)}, {~p(a)} ---> the empty clause
  auto res = runPE({clause({p(a)}), clause({~p(a)})});

  ASS_EQ(res.size(), 1);
  ASS_EQ(res[0]->length(), 0);
}

TEST_FUN(eq_residual_disequality)
{
  MY_SYNTAX_SUGAR

  // forcing the equational mode: the non-unifiable pair now leaves a residual disequality
  auto res = runPE({clause({p(a)}), clause({~p(b), q(b)}),
                    clause({q(y), ~q(f(y))})},
                   /*forceEquationally=*/true);

  ASS_EQ(res.size(), 2);
  ASS(!containsPredicate(res, p.functor()));
  bool sawDiseq = false;
  for (Clause *cl : res) {
    for (unsigned i = 0; i < cl->length(); i++) {
      Literal *l = (*cl)[i];
      sawDiseq |= (l->isEquality() && l->isNegative());
    }
  }
  ASS(sawDiseq);
}

TEST_FUN(eq_subst_computes_unifier)
{
  MY_SYNTAX_SUGAR

  // {p2(f(x),x)}, {~p2(y,a) \/ q(y)} ---> {q(f(a))}, even equationally,
  // since equality substitution resolves all the introduced disequalities away
  DECL_PRED(p2, {s, s})
  auto res = runPE({clause({p2(f(x), x)}), clause({~p2(y, a), q(y)}),
                    clause({q(y), ~q(f(y))})},
                   /*forceEquationally=*/true);

  ASS_EQ(res.size(), 2);
  ASS(!containsPredicate(res, p2.functor()));
  Clause *resolvent = theClauseOfLength(res, 1);
  ASS_EQ(resolvent->literalsOnlyToString(), "q(f(a))");
}

TEST_FUN(tautologies_dropped)
{
  MY_SYNTAX_SUGAR

  // resolving on p yields the tautology {q(x) \/ ~q(x)}; then q disappears as well
  auto res = runPE({clause({p(x), q(x)}), clause({~p(y), ~q(y)})});

  ASS_EQ(res.size(), 0);
}

TEST_FUN(self_referential_skipped)
{
  MY_SYNTAX_SUGAR

  // p occurs twice in the first clause, so it must survive
  auto res = runPE({clause({p(x), p(f(x))}), clause({~p(a)})});

  ASS_EQ(res.size(), 2);
  ASS(containsPredicate(res, p.functor()));
}

TEST_FUN(pure_predicate_clauses_deleted)
{
  MY_SYNTAX_SUGAR

  // p occurs only positively: its clause can simply be deleted
  Problem *prb = problemFromClauses({clause({p(a), q(b)}), clause({q(y), ~q(f(y))})});
  PredicateElimination pe(false, 2.0, false);
  pe.apply(*prb);
  auto res = collectClauses(*prb);

  ASS_EQ(res.size(), 1);
  ASS(!containsPredicate(res, p.functor()));
  ASS(prb->interferences.isNonEmpty()); // the model-repairing definition of p got recorded
}

TEST_FUN(growth_limits_respected)
{
  MY_SYNTAX_SUGAR

  // 3 x 3 occurrences of both p and r: eliminating either would mean
  // 9 resolvents replacing 6 clauses -- not admissible under total limit 1.0
  std::initializer_list<Clause *> cls = {
      clause({p(x), r(a)}), clause({p(x), r(b)}), clause({p(x), r(c)}),
      clause({~p(y), ~r(a)}), clause({~p(y), ~r(b)}), clause({~p(y), ~r(c)})};

  auto res = runPE(cls, false, /*totalLimit=*/1.0);
  ASS_EQ(res.size(), 6);
  ASS(containsPredicate(res, p.functor()));

  // with a benevolent limit, p gets eliminated
  // (of the 9 resolvents, 3 are tautologies; and r is self-referential in the remaining 6)
  auto res2 = runPE(cls, false, /*totalLimit=*/2.0);
  ASS_EQ(res2.size(), 6);
  ASS(!containsPredicate(res2, p.functor()));
}

TEST_FUN(duplicate_literals_removed)
{
  MY_SYNTAX_SUGAR

  // the resolvent {q(a) \/ q(a)} gets condensed to {q(a)}
  auto res = runPE({clause({p(a), q(a)}), clause({~p(x), q(x)}),
                    clause({q(y), ~q(f(y))})});

  ASS_EQ(res.size(), 2);
  Clause *resolvent = theClauseOfLength(res, 1);
  ASS_EQ(resolvent->literalsOnlyToString(), "q(a)");
}

TEST_FUN(subsumed_resolvents_not_added)
{
  MY_SYNTAX_SUGAR

  // the resolvent q(a) is subsumed by the input clause {q(a)}
  std::initializer_list<Clause *> cls = {
      clause({q(a)}), clause({p(a)}), clause({~p(x), q(x)}),
      clause({q(y), ~q(f(y))})};

  auto res = runPE(cls, false, 2.0, /*useSubsumption=*/true);
  ASS_EQ(res.size(), 2); // {q(a)} and the anchor; without subsumption we'd also keep a second copy of {q(a)}
  ASS(!containsPredicate(res, p.functor()));

  auto res2 = runPE(cls, false, 2.0, /*useSubsumption=*/false);
  ASS_EQ(res2.size(), 3);
}

/** the clause concluded by subsumption resolution -- expected to exist and be unique */
static Clause *theSRConclusion(const ClauseStack &cls)
{
  Clause *found = nullptr;
  for (Clause *cl : cls) {
    if (cl->inference().rule() == InferenceRule::FORWARD_SUBSUMPTION_RESOLUTION) {
      ASS(!found);
      found = cl;
    }
  }
  ASS(found);
  return found;
}

TEST_FUN(sr_simplifies_resolvent)
{
  MY_SYNTAX_SUGAR

  // eliminating p yields the resolvent {q(a) \/ ~r(a)}, which subsumption
  // resolution against the unit {r(a)} shrinks to {q(a)};
  // (afterwards, r is pure and {r(a)} goes away too)
  auto res = runPE({clause({r(a)}), clause({p(a)}), clause({~p(x), q(x), ~r(x)}),
                    clause({q(y), ~q(f(y))})},
                   false, 2.0, /*useSubsumption=*/true);

  ASS_EQ(res.size(), 2);
  ASS(!containsPredicate(res, p.functor()));
  ASS(!containsPredicate(res, r.functor()));
  Clause *conclusion = theClauseOfLength(res, 1);
  ASS_EQ(conclusion->literalsOnlyToString(), "q(a)");
  ASS(conclusion->inference().rule() == InferenceRule::FORWARD_SUBSUMPTION_RESOLUTION);
}

TEST_FUN(sr_on_input_pass)
{
  MY_SYNTAX_SUGAR

  // already the initial pass resolves {q(b) \/ ~r(a)} against {r(x)} down to {q(b)}
  auto res = runPE({clause({r(x)}), clause({q(b), ~r(a)}),
                    clause({q(y), ~q(f(y))})},
                   false, 2.0, /*useSubsumption=*/true);

  ASS_EQ(res.size(), 2);
  ASS(!containsPredicate(res, r.functor()));
  Clause *conclusion = theClauseOfLength(res, 1);
  ASS_EQ(conclusion->literalsOnlyToString(), "q(b)");
  ASS(conclusion->inference().rule() == InferenceRule::FORWARD_SUBSUMPTION_RESOLUTION);
}

TEST_FUN(sr_chains_to_fixpoint)
{
  MY_SYNTAX_SUGAR

  // {~p(x) \/ q(x) \/ ~r(x) \/ ~r3(x)} gets shrunk by two successive subsumption
  // resolution steps (against {r(y)} and {r3(y)}) to {~p(x) \/ q(x)} within
  // a single forwardSimplify call; eliminating p then yields {q(a)}
  DECL_PRED(r3, {s})
  unsigned srsBefore = env.statistics->predicateEliminationSRs;
  auto res = runPE({clause({p(a)}), clause({~p(x), q(x), ~r(x), ~r3(x)}),
                    clause({r(y)}), clause({r3(y)}),
                    clause({q(y), ~q(f(y))})},
                   false, 2.0, /*useSubsumption=*/true);

  ASS_EQ(env.statistics->predicateEliminationSRs - srsBefore, 2);
  ASS_EQ(res.size(), 2);
  ASS(!containsPredicate(res, p.functor()));
  ASS(!containsPredicate(res, r.functor()));
  ASS(!containsPredicate(res, r3.functor()));
  Clause *resolvent = theClauseOfLength(res, 1);
  ASS_EQ(resolvent->literalsOnlyToString(), "q(a)");
  ASS(resolvent->inference().rule() == InferenceRule::PREDICATE_ELIMINATION);
}

TEST_FUN(duplicate_literals_in_input)
{
  MY_SYNTAX_SUGAR

  // clauses can still carry duplicate literals when they reach predicate elimination
  // (e.g. created by EqResWithDeletion from p(X) \/ p(a) \/ X != a);
  // they must be removed on input, since the multi-literal matching behind our
  // subsumption relies on clauses being duplicate-free -- feeding {p(a) \/ p(a)}
  // as the query against the indexed {p(x) \/ ~p(y)} used to "conclude" the empty clause!
  auto res = runPE({clause({p(a), p(a)}), clause({p(x), ~p(y)})},
                   false, 2.0, /*useSubsumption=*/true);

  ASS_EQ(res.size(), 2);
  for (Clause *cl : res) {
    ASS_G(cl->length(), 0); // and in particular: no bogus empty clause
  }
  Clause *dedup = theClauseOfLength(res, 1);
  ASS_EQ(dedup->literalsOnlyToString(), "p(a)");
}

TEST_FUN(sr_multiliteral)
{
  MY_SYNTAX_SUGAR

  // a multi-literal side premise {q(x) \/ ~r(x)} resolves {q(a) \/ r(a) \/ w(a)}
  // down to {q(a) \/ w(a)} (exercising the full multi-literal matching, not just the unit shortcut)
  DECL_PRED(w, {s})
  auto res = runPE({clause({q(x), ~r(x)}), clause({q(y), ~q(f(y))}), clause({w(y), ~w(f(y))}),
                    clause({q(a), r(a), w(a)})},
                   false, 2.0, /*useSubsumption=*/true);

  ASS_EQ(res.size(), 3); // the conclusion and the two anchors ({q(x) \/ ~r(x)} dies with pure r)
  ASS(!containsPredicate(res, r.functor()));
  Clause *conclusion = theSRConclusion(res);
  ASS_EQ(conclusion->length(), 2);
}

TEST_FUN(empty_resolvent_against_nonempty_index)
{
  MY_SYNTAX_SUGAR

  // eliminating p produces the empty clause, which is then handed to forwardSimplify
  // while the index already holds the q-anchor; the empty clause has nothing to match on,
  // so it must be passed through rather than fed to the multi-literal matcher
  auto res = runPE({clause({p(a)}), clause({~p(a)}),
                    clause({q(y), ~q(f(y))})},
                   false, 2.0, /*useSubsumption=*/true);

  ASS_EQ(res.size(), 2);
  ASS(!containsPredicate(res, p.functor()));
  ASS_EQ(theClauseOfLength(res, 0)->length(), 0);
}

TEST_FUN(input_tautologies_dropped)
{
  MY_SYNTAX_SUGAR

  // tautologies can still reach predicate elimination; they are dropped on input,
  // both because they are useless and because the multi-literal matching assumes
  // no clause contains two complementary literals
  auto res = runPE({clause({p(a), ~p(a)}), clause({q(y), ~q(f(y))})},
                   false, 2.0, /*useSubsumption=*/true);

  ASS_EQ(res.size(), 1);
  ASS(!containsPredicate(res, p.functor()));
}

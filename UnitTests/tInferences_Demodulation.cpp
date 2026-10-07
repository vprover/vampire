/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Test/SyntaxSugar.hpp"
#include "Inferences/ForwardDemodulation.hpp"
#include "Inferences/BackwardDemodulation.hpp"

#include "Test/FwdBwdSimplificationTester.hpp"

using namespace std;
using namespace Kernel;
using namespace Inferences;
using namespace Test;

/**
 * NECESSARY: We need to tell the tester which syntax sugar to import for creating terms & clauses.
 * See Test/SyntaxSugar.hpp for which kinds of syntax sugar are available
 */
#define MY_SYNTAX_SUGAR                                                                                       \
  DECL_DEFAULT_VARS                                                                                           \
  DECL_DEFAULT_SORT_VARS                                                                                      \
  DECL_VAR(u, 3)                                                                                              \
  DECL_SORT(s)                                                                                                \
  DECL_SORT(s2)                                                                                               \
  DECL_LEFT_FUNC(left, {s}, s)                                                                                \
  DECL_RIGHT_FUNC(right, {s}, s)                                                                              \
  DECL_POLY_CONST(h, 1, alpha)                                                                                \
  DECL_FUNC(f, {s, s}, s)                                                                                     \
  DECL_FUNC(g, {s}, s)                                                                                        \
  DECL_CONST(a, s)                                                                                            \
  DECL_CONST(b, s)                                                                                            \
  DECL_CONST(c, s2)                                                                                           \
  DECL_PRED (p, {s})                                                                                          \
  DECL_PRED (q, {s})

namespace {

// TODO add tests for higher-order case too
inline auto tester() {
  return FwdBwdSimplification::TestCase<ForwardDemodulation<false>, BackwardDemodulation<false>>()
    .options({ { "term_ordering", "lpo" } }); // use LPO as KBO fails due to caching things in terms
}

// demodulation with preordered equation
TEST_SIMPLIFICATION(test01,
  tester()
    .simplifyWith({ clause({ f(x,y) == x }) })
    .toSimplify({ clause({ ~p(f(a,b)) }) })
    .expected({ clause({ ~p(a) }) })
)

// demodulation with postordered equation
TEST_SIMPLIFICATION(test02,
  tester()
    .simplifyWith({ clause({ f(x,y) == f(y,x) }) })
    .toSimplify({ clause({ ~p(f(b,a)) }) })
    .expected({ clause({ ~p(f(a,b)) }) })
)

// demodulation fails with postordered equation
TEST_SIMPLIFICATION(test03,
  tester()
    .simplifyWith({ clause({ f(x,y) == f(y,x) }) })
    .toSimplify({ clause({ ~p(f(a,b)) }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

// encompassment demodulation
TEST_SIMPLIFICATION(test04,
  tester()
    .simplifyWith({ clause({ f(x,y) == f(y,x) }) })
    .toSimplify({ clause({ f(b,a) == a }) })
    .expected({ clause({ f(a,b) == a }) })
)

// encompassment demodulation fails due to equation being equally general and demodulator being bigger
TEST_SIMPLIFICATION(test05,
  tester()
    .simplifyWith({ clause({ f(b,a) == f(a,b) }) })
    .toSimplify({ clause({ f(b,a) == a }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

// drc=ordering fails due to other side being smaller than the terms we demodulate into
TEST_SIMPLIFICATION(test06,
  tester()
    .simplifyWith({ clause({ f(a,b) == a }) })
    .toSimplify({ clause({ f(a,b) == b }) })
    .expected({ clause({ a == b }) })
    .options({ { "term_ordering", "lpo" }, { "demodulation_redundancy_check", "ordering" } });
)

// drc=ordering fails due to other side being smaller than the terms we demodulate into
TEST_SIMPLIFICATION(test07,
  tester()
    .simplifyWith({ clause({ f(x,y) == f(y,x) }) })
    .toSimplify({ clause({ f(b,a) == a }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
    .options({ { "term_ordering", "lpo" }, { "demodulation_redundancy_check", "ordering" } });
)

// drc=ordering does not care about ordering of equations
TEST_SIMPLIFICATION(test08,
  tester()
    .simplifyWith({ clause({ f(b,a) == f(a,b) }) })
    .toSimplify({ clause({ f(b,a) == a }) })
    .expected({ clause({ f(a,b) == a }) })
    .options({ { "term_ordering", "lpo" }, { "demodulation_redundancy_check", "off" } });
)

// non-preordered equation is not used with bd/fd=preordered
TEST_SIMPLIFICATION(test09,
  tester()
    .simplifyWith({ clause({ f(x,y) == f(y,x) }) })
    .toSimplify({ clause({ p(f(b,a)) }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
    .options({ { "term_ordering", "lpo" }, { "backward_demodulation", "preordered" }, { "forward_demodulation", "preordered" } });
)

// TODO this should be a simplification, but maybe not worth checking,
// otherwise I'm not sure if we should even handle variable equations
//
// demodulation with variable equality
TEST_SIMPLIFICATION(test10,
  tester()
    .simplifyWith({ clause({ TermSugar(TermList::var(0), s) == y }) })
    .toSimplify({ clause({ f(b,a) == a }) })
    // .expected({ clause({ x == a }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

// demodulation of the smaller side of an equation
TEST_SIMPLIFICATION(test11,
  tester()
    .simplifyWith({ clause({ f(b,a) == f(a,b) }) })
    .toSimplify({ clause({ g(f(x,b)) == f(b,a) }) })
    .expected({ clause({ g(f(x,b)) == f(a,b) }) })
)

// demodulation results in equational tautology
TEST_SIMPLIFICATION(test12,
  tester()
    .simplifyWith({ clause({ f(b,a) == f(a,b) }) })
    .toSimplify({ clause({ g(f(b,a)) == g(f(a,b)) }) })
    .expected({ /* nothing */ })
    .justifications({ clause({ f(b,a) == f(a,b) }) })
)

// demodulation into non-unit clause
TEST_SIMPLIFICATION(test13,
  tester()
    .simplifyWith({ clause({ f(b,a) == f(a,b) }) })
    .toSimplify({ clause({ f(b,a) == a, ~p(x) }) })
    .expected({ clause({ f(a,b) == a, ~p(x) }) })
)

// no demodulation due to different colors
TEST_SIMPLIFICATION(test14,
  tester()
    .simplifyWith({ clause({ f(x,y) == left(y) }) })
    .toSimplify({ clause({ g(f(a,b)) == right(a) }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

// demodulation with colors
TEST_SIMPLIFICATION(test15,
  tester()
    .simplifyWith({ clause({ f(x,y) == left(y) }) })
    .toSimplify({ clause({ g(f(a,b)) == left(a) }) })
    .expected({ clause({ g(left(b)) == left(a) }) })
)

// demodulation with variable equality
TEST_SIMPLIFICATION(test16,
  tester()
    .simplifyWith({ clause({ TermSugar(TermList::var(0), s) == b }) })
    .toSimplify({ clause({ f(b,a) != a }) })
    .expected({ clause({ b != a }) })
)

TEST_SIMPLIFICATION(test17,
  tester()
    .simplifyWith({ clause({ x == h(y) }) })
    .toSimplify({ clause({ f(f(b,a),a) != a }) })
    .expected({ clause({ h(s) != a }) })
)

// demodulation_cache: the same scenarios with the cache of failed lookups enabled.
// Each test visits the same term in two clauses, so the second visit is served
// from the cache; no result may change.
inline auto cachedTester() {
  return FwdBwdSimplification::TestCase<ForwardDemodulation<false>, BackwardDemodulation<false>>()
    .options({ { "term_ordering", "lpo" }, // use LPO as KBO fails due to caching things in terms
               { "demodulation_cache", "on" } });
}

// the lookup finds only a demodulator rejected by the ordering check: an applicability
// failure is recorded, and the second visit of the same term is skipped
TEST_SIMPLIFICATION(test20,
  cachedTester()
    .simplifyWith({ clause({ f(x,y) == f(y,x) }) })
    .toSimplify({ clause({ ~p(f(a,b)) }), clause({ ~q(f(a,b)) }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

// a demodulator rejected by the redundancy check must not be recorded as a failure:
// the same term still has to rewrite the next clause
TEST_SIMPLIFICATION(test21,
  cachedTester()
    .simplifyWith({ clause({ f(b,a) == f(a,b) }) })
    .toSimplify({ clause({ f(b,a) == a }), clause({ ~p(f(b,a)) }) })
    .expected({ clause({ ~p(f(a,b)) }) })
)

// with fd=preordered the non-preordered demodulator is not used; the failure is
// recorded and the second visit of the same term is skipped
TEST_SIMPLIFICATION(test22,
  cachedTester()
    .simplifyWith({ clause({ f(x,y) == f(y,x) }) })
    .toSimplify({ clause({ p(f(a,b)) }), clause({ q(f(a,b)) }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
    .options({ { "term_ordering", "lpo" },
               { "demodulation_cache", "on" },
               { "forward_demodulation", "preordered" },
               { "backward_demodulation", "preordered" } })
)

// lookups that find nothing are recorded and skipped on the second visit
TEST_SIMPLIFICATION(test23,
  cachedTester()
    .simplifyWith({ clause({ f(x,y) == x }) })
    .toSimplify({ clause({ ~p(g(a)) }), clause({ ~q(g(a)) }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

// successful rewrites must not be recorded as failures: the same term rewrites again
TEST_SIMPLIFICATION(test24,
  cachedTester()
    .simplifyWith({ clause({ f(x,y) == x }) })
    .toSimplify({ clause({ ~p(f(a,b)) }), clause({ ~q(f(a,b)) }) })
    .expected({ clause({ ~p(a) }), clause({ ~q(a) }) })
)

// a demodulator rejected by the color check must not be recorded as a failure: the
// same term still has to rewrite a clause of the demodulator's color
TEST_SIMPLIFICATION(test25,
  cachedTester()
    .simplifyWith({ clause({ f(x,y) == left(y) }) })
    .toSimplify({ clause({ g(f(a,b)) == right(a) }), clause({ g(f(a,b)) == left(a) }) })
    .expected({ clause({ g(left(b)) == left(a) }) })
)

// a rewrite into an equational tautology is no failure: the same term still rewrites
// (and discards) the next clause
TEST_SIMPLIFICATION(test26,
  cachedTester()
    .simplifyWith({ clause({ f(b,a) == f(a,b) }) })
    .toSimplify({ clause({ g(f(b,a)) == g(f(a,b)) }), clause({ g(f(b,a)) == g(f(a,b)), ~p(x) }) })
    .expected({ /* nothing */ })
    .justifications({ clause({ f(b,a) == f(a,b) }) })
)

TEST_SIMPLIFICATION(test18,
  tester()
    .simplifyWith({ clause({ y == h(x) }) })
    .toSimplify({ clause({ f(f(b,a),a) != a }) })
    .expected({ clause({ h(s) != a }) })
)

TEST_SIMPLIFICATION(test19,
  tester()
    .simplifyWith({ clause({ x == c }) })
    .toSimplify({ clause({ f(f(b,a),a) != a }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

}

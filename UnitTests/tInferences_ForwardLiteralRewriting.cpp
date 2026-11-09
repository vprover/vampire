/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Test/FwdBwdSimplificationTester.hpp"
#include "Test/SyntaxSugar.hpp"

#include "Inferences/ForwardLiteralRewriting.hpp"

using namespace Test;

namespace {

/**
 * NECESSARY: We need to tell the tester which syntax sugar to import for creating terms & clauses.
 * See Test/SyntaxSugar.hpp for which kinds of syntax sugar are available
 */
#define MY_SYNTAX_SUGAR                                                                                       \
  DECL_DEFAULT_VARS                                                                                           \
  DECL_DEFAULT_SORT_VARS                                                                                      \
  DECL_VAR(u, 3)                                                                                              \
  DECL_VAR(v, 4)                                                                                              \
  DECL_VAR(w, 5)                                                                                              \
  DECL_SORT(s)                                                                                                \
  DECL_TYPE_CON(tc, 2)                                                                                        \
  DECL_POLY_FUNC(h, 2, { alpha, beta }, tc(beta,alpha))                                                       \
  DECL_FUNC(f, {s, s}, s)                                                                                     \
  DECL_FUNC(g, {s}, s)                                                                                        \
  DECL_CONST(a, s)                                                                                            \
  DECL_CONST(b, s)                                                                                            \
  DECL_PRED (p, {s})                                                                                          \
  DECL_PRED (q, {s})

inline auto tester() {
  return FwdBwdSimplification::TestCase<ForwardLiteralRewriting, DummyBwdRule>();
}

// one side of the rule is missing
TEST_FWD_SIMPLIFICATION(fail01,
  tester()
    .simplifyWith({
      clause({ ~p(f(x,y)), q(x) }),
    })
    .toSimplify({ clause({ p(f(a,b)) }) })
    .justifications({ /* nothing */ })
    .expected({ /* nothing */ })
)

// other side of the rule is missing
TEST_FWD_SIMPLIFICATION(fail02,
  tester()
    .simplifyWith({
      clause({ p(f(x,y)), ~q(x) }),
    })
    .toSimplify({ clause({ ~p(f(a,b)) }) })
    .justifications({ /* nothing */ })
    .expected({ /* nothing */ })
)

// sides are not variants of each other
TEST_FWD_SIMPLIFICATION(fail03,
  tester()
    .simplifyWith({
      clause({ ~p(f(x,y)), q(x) }),
      clause({ p(f(x,y)), ~q(y) }),
    })
    .toSimplify({ clause({ ~p(f(a,b)) }) })
    .justifications({ /* nothing */ })
    .expected({ /* nothing */ })
)

// positive case
TEST_FWD_SIMPLIFICATION(success01,
  tester()
    .simplifyWith({
      clause({ ~p(f(x,y)), q(x) }),
      clause({ p(f(x,y)), ~q(x) }),
    })
    .toSimplify({ clause({ p(f(a,b)) }) })
    .justifications({ clause({ ~p(f(x,y)), q(x) }) })
    .expected({ clause({ q(a) }) })
)

// negative case
TEST_FWD_SIMPLIFICATION(success02,
  tester()
    .simplifyWith({
      clause({ ~p(f(x,y)), q(x) }),
      clause({ p(f(x,y)), ~q(x) }),
    })
    .toSimplify({ clause({ ~p(f(a,b)) }) })
    .justifications({ clause({ p(f(x,y)), ~q(x) }) })
    .expected({ clause({ ~q(a) }) })
)

// fixed bug with variable normalization in substitutions coming from code trees
TEST_FWD_SIMPLIFICATION(bug01,
  tester()
    .simplifyWith({
      clause({ h(x,y,z,u) != h(x,y,v,w), z.sort(x) == v }),
      clause({ h(x,y,z,u) == h(x,y,v,w), z.sort(x) != v }),
    })
    .toSimplify({ clause({ h(x,y,z,u) == h(x,y,v,w), z.sort(x) != v, u.sort(y) == w }) })
    .justifications({ clause({ h(x,y,z,u) != h(x,y,v,w), z.sort(x) == v }) })
    .expected({ clause({ z.sort(x) == v, z.sort(x) != v, u.sort(y) == w }) })
)

}

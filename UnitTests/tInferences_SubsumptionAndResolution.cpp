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
#include "Inferences/ForwardSubsumptionAndResolution.hpp"
#include "Inferences/BackwardSubsumptionAndResolution.hpp"

#include "Test/FwdBwdSimplificationTester.hpp"

using namespace std;
using namespace Kernel;
using namespace Inferences;
using namespace Test;

#define MY_SYNTAX_SUGAR  \
 __ALLOW_UNUSED( \
    DECL_DEFAULT_VARS \
    DECL_VAR(x1, 1) \
    DECL_VAR(x2, 2) \
    DECL_VAR(x3, 3) \
    DECL_VAR(x4, 4) \
    DECL_VAR(x5, 5) \
    DECL_VAR(x6, 6) \
    DECL_VAR(x7, 7) \
    DECL_VAR(y1, 11) \
    DECL_VAR(y2, 12) \
    DECL_VAR(y3, 13) \
    DECL_VAR(y4, 14) \
    DECL_VAR(y5, 15) \
    DECL_VAR(y6, 16) \
    DECL_VAR(y7, 17) \
    DECL_SORT(s) \
    DECL_CONST(c, s) \
    DECL_CONST(d, s) \
    DECL_CONST(e, s) \
    DECL_FUNC(f, {s}, s) \
    DECL_FUNC(f2, {s, s}, s) \
    DECL_FUNC(f3, {s, s, s}, s) \
    DECL_FUNC(g, {s}, s) \
    DECL_FUNC(g2, {s, s}, s) \
    DECL_FUNC(h, {s}, s) \
    DECL_FUNC(h2, {s, s}, s) \
    DECL_FUNC(i, {s}, s) \
    DECL_FUNC(i2, {s, s}, s) \
    DECL_PRED(p, {s}) \
    DECL_PRED(p2, {s, s}) \
    DECL_PRED(p3, {s, s, s}) \
    DECL_PRED(q, {s}) \
    DECL_PRED(q2, {s, s}) \
    DECL_PRED(r, {s}) \
    DECL_PRED(r2, {s, s}) \
  )

namespace SubsumptionAndResolutionTester {

inline auto tester() {
  return FwdBwdSimplification::TestCase()
    .fwd(new ForwardSubsumptionAndResolution())
    .bwd(new BackwardSubsumptionAndResolution(/*subsumption=*/true, /*subsumptionByUnitsOnly=*/false, /*subsumptionResolution=*/true, /*srByUnitsOnly=*/false));
}

// Note: most of these tests were taken from the SAT subsumption test suite

// positive subsumptions

TEST_SIMPLIFICATION(pos_sub_test01,
  tester()
    .simplifyWith({ clause({ p2(x, f(y)) }) })
    .toSimplify({ clause({ p2(c, f(d)) }) })
    .expected({ /* nothing */ })
)

TEST_SIMPLIFICATION(pos_sub_test02,
  tester()
    .simplifyWith({ clause({ ~p2(g(x), f(y)) }) })
    .toSimplify({ clause({ ~p2(g(x), f(x)) }) })
    .expected({ /* nothing */ })
)

TEST_SIMPLIFICATION(pos_sub_test03,
  tester()
    .simplifyWith({ clause({ p3(x1, x2, x3), p3(f(x2), x4, x4) }) })
    .toSimplify({ clause({ p3(f(c), d, y1), p3(f(d), c, c) }) })
    .expected({ /* nothing */ })
)

TEST_SIMPLIFICATION(pos_sub_test04,
  tester()
    .simplifyWith({ clause({ p3(x1, x2, x3), p3(f(x2), x4, x4) }) })
    .toSimplify({ clause({ p3(f(c), d, y1), p3(f(d), c, c), r(x1) }) })
    .expected({ /* nothing */ })
)

TEST_SIMPLIFICATION(pos_sub_test05,
  tester()
    .simplifyWith({ clause({ p(f2(f(g(x1)), x1)), c == g(x1) }) })
    .toSimplify({ clause({ g(y1) == c, p(f2(f(g(y1)), y1)) }) })
    .expected({ /* nothing */ })
)

TEST_SIMPLIFICATION(pos_sub_test06,
  tester()
    .simplifyWith({ clause({ f2(x1, x2) == c, ~p2(x1, x3), p2(f(f2(x1, x2)), f(x3)) }) })
    .toSimplify({ clause({ c == f2(x3, y2), ~p2(x3, y1), p2(f(f2(x3, y2)), f(y1)) }) })
    .expected({ /* nothing */ })
)

TEST_SIMPLIFICATION(pos_sub_test07,
  tester()
    .simplifyWith({ clause({ p(f2(f(e), g2(x4, x3))), p2(f2(f(e), g2(x4, x3)), x3), f(e) == g2(x4, x3) }) })
    .toSimplify({ clause({ p(f2(f(e), g2(y1, y3))), p2(f2(f(e), g2(y1, y3)), y3), f(e) == g2(y1, y3) }) })
    .expected({ /* nothing */ })
)

TEST_SIMPLIFICATION(pos_sub_test08,
  tester()
    .simplifyWith({ clause({ p3(y7, f(y1), x4), ~p3(y7, y1, x4) }) })
    .toSimplify({ clause({ p3(x6, f(y3), d), ~p3(x6, y3, d) }) })
    .expected({ /* nothing */ })
)

// negative subsumptions

TEST_SIMPLIFICATION(neg_sub_test01,
  tester()
    .simplifyWith({ clause({ p2(f2(g2(x1, x2), x3), x3), p2(f2(g2(x1, x2), x3), x2), g2(x1, x2) == x3 }) })
    .toSimplify({ clause({ p2(f2(g2(y1, y2), y2), y2), g2(y1, y2) == y2, ~p2(f2(g2(y1, y2), y2), g2(y1, y2)) }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

TEST_SIMPLIFICATION(neg_sub_test02,
  tester()
    .simplifyWith({ clause({ ~p2(x1, x2), p(x1) }) })
    .toSimplify({ clause({ p(y1), ~p(f(f2(f2(y2, y2), f2(y2, y3)))), ~p(y3), ~p(y2) }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

TEST_SIMPLIFICATION(neg_sub_test03,
  tester()
    .simplifyWith({ clause({ p2(y5, f(f2(c, x1))), ~p(c), ~p(y5) }) })
    .toSimplify({ clause({ ~q(f(d)), p2(c, f(f2(c, x4))), r(e), ~p(c), d == g(c) }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

TEST_SIMPLIFICATION(neg_sub_test04,
  tester()
    .simplifyWith({ clause({ p2(y5, f(f2(x1, c))), ~p(c), ~p(y5) }) })
    .toSimplify({ clause({ ~q(d), p2(c, f(f2(x4, c))), r(d), ~p(c), d == g(c) }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

TEST_SIMPLIFICATION(neg_sub_test05,
  tester()
    .simplifyWith({ clause({ p(x1), x1 == f(x2), p(x2) }) })
    .toSimplify({ clause({ p(y1), y1 == f(y1) }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

TEST_SIMPLIFICATION(neg_sub_test06,
  tester()
    .simplifyWith({ clause({ p(x1), x1 == f(x2), p(x2), q(x1) }) })
    .toSimplify({ clause({ p(y1), y1 == f(y1), q(y2), r(y3) }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

TEST_SIMPLIFICATION(neg_sub_test07,
  tester()
    .simplifyWith({ clause({ p(f(x1)), p(f(x2)) }) })
    .toSimplify({ clause({ p(f(y1)), p(g(y2)) }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

// positive subsumption resolutions

TEST_SIMPLIFICATION(pos_sub_res_test01,
  tester()
    .simplifyWith({ clause({ ~p(x1), q(x1) }) })
    .toSimplify({ clause({ p(c), q(c), r(e) }) })
    .expected({ clause({ q(c), r(e) }) })
)

TEST_SIMPLIFICATION(pos_sub_res_test02,
  tester()
    .simplifyWith({ clause({ p2(x1, x2), p2(f(x2), x3) }) })
    .toSimplify({ clause({ ~p2(f(y1), d), p2(g(y1), c), ~p2(f(c), e) }) })
    .expected({ clause({ ~p2(f(y1), d), p2(g(y1), c) }) })
)

TEST_SIMPLIFICATION(pos_sub_res_test03,
  tester()
    .simplifyWith({ clause({ p3(x2, f(x2), e) }) })
    .toSimplify({ clause({ p3(f(e), x5, x5), ~p3(x4, f(x4), e) }) })
    .expected({ clause({ p3(f(e), x5, x5) }) })
)

TEST_SIMPLIFICATION(pos_sub_res_test04,
  tester()
    .simplifyWith({ clause({ p(c) }) })
    .toSimplify({ clause({ ~p(c) }) })
    .expected({ clause({}) })
)

TEST_SIMPLIFICATION(pos_sub_res_test05,
  tester()
    .simplifyWith({ clause({ ~p(f(x1)), q(x1) }) })
    .toSimplify({ clause({ ~p2(x2, x5), q(x2), p(f(x2)), ~q(g(x5)) }) })
    .expected({ clause({ ~p2(x2, x5), q(x2), ~q(g(x5)) }) })
)

// TODO I'm assuming these give different results for forwards and backwards, so they cannot be enabled
// TEST_SIMPLIFICATION(pos_sub_res_test06,
//   tester()
//     .simplifyWith({ clause({ p(f2(y7, x6)), p2(y7, x6) }) })
//     .toSimplify({ clause({ p2(f(g(x5)), y4), ~p(f2(f(g(x5)), y4)), ~p2(f2(f(g(x5)), y4), x5) }) })
//     .expected({ /* nothing */ })
//     .justifications({ /* nothing */ })
// )

// TEST_SIMPLIFICATION(pos_sub_res_test07,
//   tester()
//     .simplifyWith({ clause({ p(f2(y7, x6)), p2(y7, x6) }) })
//     .toSimplify({ clause({ p2(f(g(x5)), y4), ~p(f2(f(g(x5)), y4)), ~p2(f2(f(g(x5)), y4), x5) }) })
//     .expected({ /* nothing */ })
//     .justifications({ /* nothing */ })
// )

// TEST_SIMPLIFICATION(pos_sub_res_test08,
//   tester()
//     .simplifyWith({ clause({ ~p2(y7, d) }) })
//     .toSimplify({ clause({ ~p(x6), ~p(x5), ~p2(f(f2(f2(x5, x5), f2(x5, x6))), x6), p2(f2(f2(x5, x5), f2(x5, x6)), d) }) })
//     .expected({ /* nothing */ })
//     .justifications({ /* nothing */ })
// )

// TEST_SIMPLIFICATION(pos_sub_res_test09,
//   tester()
//     .simplifyWith({ clause({ ~p3(d, y7, d), ~p3(y7, e, c) }) })
//     .toSimplify({ clause({ p3(d, x6, d), ~p3(x6, e, c) }) })
//     .expected({ /* nothing */ })
//     .justifications({ /* nothing */ })
// )

// TEST_SIMPLIFICATION(pos_sub_res_test10,
//   tester()
//     .simplifyWith({ clause({ p2(y7, x6), f2(y7, x6) == f2(f3(x5, y4, x4), x4), p2(y4, x4) }) })
//     .toSimplify({ clause({ ~p2(g2(h2(y3, x2), x2), x7), f2(g2(h2(y3, x2), x2), x7) == f2(f3(y6, g2(h2(y3, x2), x2), x7), x7) }) })
//     .expected({ /* nothing */ })
//     .justifications({ /* nothing */ })
// )

// TEST_SIMPLIFICATION(pos_sub_res_test11,
//   tester()
//     .simplifyWith({ clause({ p2(y7, x6), ~q2(x5, x6), ~p2(y7, x5) }) })
//     .toSimplify({ clause({ p2(f2(y4, x6), y4), ~p2(x6, y7), ~r2(y4, y7), ~p2(x6, d), ~q2(y4, d), ~q2(y7, d) }) })
//     .expected({ /* nothing */ })
//     .justifications({ /* nothing */ })
// )

// TEST_SIMPLIFICATION(pos_sub_res_test12,
//   tester()
//     .simplifyWith({ clause({ p(d) }) })
//     .toSimplify({ clause({ q(d), ~p(d) }) })
//     .expected({ /* nothing */ })
//     .justifications({ /* nothing */ })
// )

// negative subsumption resolutions

TEST_SIMPLIFICATION(neg_sub_res_test01,
  tester()
    .simplifyWith({ clause({ ~p(x1), q(x1) }) })
    .toSimplify({ clause({ p(c), q(d), r(e) }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

TEST_SIMPLIFICATION(neg_sub_res_test02,
  tester()
    .simplifyWith({ clause({ ~p(x1), ~q(x2) }) })
    .toSimplify({ clause({ p(c), q(d), r(e) }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

TEST_SIMPLIFICATION(neg_sub_res_test03,
  tester()
    .simplifyWith({ clause({ ~p(x1), r(c) }) })
    .toSimplify({ clause({ p(c), q(d), r(e) }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

TEST_SIMPLIFICATION(neg_sub_res_test04,
  tester()
    .simplifyWith({ clause({ ~p(x1), p2(x1, x2) }) })
    .toSimplify({ clause({ p(c), q(d), r(e) }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

TEST_SIMPLIFICATION(neg_sub_res_test05,
  tester()
    .simplifyWith({ clause({ p3(x1, x2, x2), ~p3(x2, c, c) }) })
    .toSimplify({ clause({ p3(y1, c, c), ~p3(y1, y2, y2) }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

TEST_SIMPLIFICATION(neg_sub_res_test06,
  tester()
    .simplifyWith({ clause({ p3(y7, x6, x6), ~p3(y7, d, d) }) })
    .toSimplify({ clause({ p3(x5, d, d), ~p3(x5, x6, x6) }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

TEST_SIMPLIFICATION(neg_sub_res_test07,
  tester()
    .simplifyWith({ clause({ ~p3(y7, d, d), p3(y7, x6, x6) }) })
    .toSimplify({ clause({ ~p3(x5, y4, f(f2(x4, f(y3)))), p3(x2, d, d), ~p3(x7, x4, y3), ~p3(x2, f2(x5, y4), x7) }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

TEST_SIMPLIFICATION(neg_sub_res_test08,
  tester()
    .simplifyWith({ clause({ ~p3(y7, d, d), p3(y7, x6, x6) }) })
    .toSimplify({ clause({ ~p3(x5, x6, x6), p3(d, d, x5) }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

TEST_SIMPLIFICATION(neg_sub_res_test09,
  tester()
    .simplifyWith({ clause({ ~p3(d, y7, d), p3(x6, y7, x6) }) })
    .toSimplify({ clause({ p3(d, x5, d), ~p3(y4, f(y4), f(x5)) }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

TEST_SIMPLIFICATION(neg_sub_res_test10,
  tester()
    .simplifyWith({ clause({ ~p3(d, d, d), p3(f(f(y7)), d, y7) }) })
    .toSimplify({ clause({ p3(d, x6, x6) }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

TEST_SIMPLIFICATION(neg_sub_res_test11,
  tester()
    .simplifyWith({ clause({ p2(y7, d), p2(e, y7), e == y7 }) })
    .toSimplify({ clause({ ~p2(x6, x5), ~p2(y7, x6), p2(y7, x5) }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

TEST_SIMPLIFICATION(neg_sub_res_test12,
  tester()
    .simplifyWith({ clause({ f2(y1, y3) == x1, ~p2(g2(x1, f2(y1, y3)), x1), ~p2(g2(x1, f2(y1, y3)), y1), ~p2(g2(x1, f2(y1, y3)), y3) }) })
    .toSimplify({ clause({ p2(g2(x2, f2(y1, y3)), x2), f2(y1, y3) == x2, p2(g2(x2, f2(y1, y3)), y3) }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

}

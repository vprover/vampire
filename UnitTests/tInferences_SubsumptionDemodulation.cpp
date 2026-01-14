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
#include "Inferences/ForwardSubsumptionDemodulation.hpp"
#include "Inferences/BackwardSubsumptionDemodulation.hpp"

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
  DECL_VAR(u, 3)                                                                                              \
  DECL_SORT(s)                                                                                                \
  DECL_FUNC(f, {s, s}, s)                                                                                     \
  DECL_FUNC(g, {s}, s)                                                                                        \
  DECL_CONST(a, s)                                                                                            \
  DECL_CONST(b, s)                                                                                            \
  DECL_PRED (p, {s})                                                                                          \
  DECL_PRED (q, {s})                                                                                          \

namespace SubsumptionDemodulationTester {

inline auto tester() {
  return FwdBwdSimplification::TestCase()
    .fwd(new ForwardSubsumptionDemodulation(/*doSubsumption=*/false, /*enableOrderingOptimizations=*/true))
    .bwd(new BackwardSubsumptionDemodulation(/*enableOrderingOptimizations=*/true));
}

// subsumption demodulation with preordered equation
TEST_SIMPLIFICATION(test01,
  tester()
    .simplifyWith({ clause({ f(x,y) == x, g(x) != a }) })
    .toSimplify({ clause({ ~p(f(a,b)), g(a) != a }) })
    .expected({ clause({ ~p(a), g(a) != a }) })
)

// subsumption demodulation does not happen due to too many literals in simplifierwith preordered equation
TEST_SIMPLIFICATION(test02,
  tester()
    .simplifyWith({ clause({ f(x,y) == x, g(x) != a, q(a) }) })
    .toSimplify({ clause({ ~p(f(a,b)), g(a) != a }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

// subsumption demodulation does not happen due to unorientable equation
TEST_SIMPLIFICATION(test03,
  tester()
    .simplifyWith({ clause({ f(x,x) == g(y), g(x) != a }) })
    .toSimplify({ clause({ ~p(f(a,b)), g(a) != a }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

// subsumption demodulation does not happen due to post-ordering check
TEST_SIMPLIFICATION(test04,
  tester()
    .simplifyWith({ clause({ f(x,y) == f(y,x), g(x) != y }) })
    .toSimplify({ clause({ ~p(f(a,b)), g(a) != b }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

// subsumption demodulation does not happen due to the rewriting instance being larger than the rewritten clause
TEST_SIMPLIFICATION(test05,
  tester()
    .simplifyWith({ clause({ f(x,y) == f(y,x), g(x) != y }) })
    .toSimplify({ clause({ f(a,b) == a, g(a) != b }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

// subsumption demodulation happens because we rewrite the second largest term in clause
TEST_SIMPLIFICATION(test06,
  tester()
    .simplifyWith({ clause({ f(x,y) == g(y), g(x) != y }) })
    .toSimplify({ clause({ f(a,b) == g(g(g(b))), g(a) != b }) })
    .expected({ clause({ g(b) == g(g(g(b))), g(a) != b }) })
)

}

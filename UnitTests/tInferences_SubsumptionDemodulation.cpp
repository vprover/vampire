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

}

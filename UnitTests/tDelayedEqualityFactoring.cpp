/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */


#include "Inferences/DelayedUnification.hpp"
#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Test/TestUtils.hpp"
#include "Test/GenerationTester.hpp"
#include "Kernel/KBO.hpp"

using namespace Test;
using namespace Test::Generation;

inline Ordering* testOrdering() {
  static Ordering* ord = KBO::newPlainKBO();
  return ord;
}


REGISTER_GEN_TESTER(DelayedEqualityFactoring, testOrdering(), env.options)

#define MY_SYNTAX_SUGAR                                                                             \
  DECL_DEFAULT_VARS                                                                                 \
  DECL_SORT(s)                                                                                      \
  DECL_CONST(a, s)                                                                                  \
  DECL_CONST(b, s)                                                                                  \
  DECL_CONST(c, s)                                                                                  \
  DECL_FUNC(f, {s}, s)                                                                              \
  DECL_FUNC(g, {s}, s)                                                                              \
  DECL_FUNC(f2, {s,s}, s)                                                                           \
  DECL_FUNC(g2, {s,s}, s)                                                                           \
  DECL_PRED(P, {s})                                                                                 \

TEST_GENERATION(test_01,
    Generation::TestCase()
      .input(    clause({ selected(x == b), x == a  }) )
      .expected(exactly(
            clause({ a != b, x == b  })
      ))
    )

TEST_GENERATION(test_02,
    Generation::TestCase()
      .input(    clause({ selected(f(x) == b), x == g(x)  }) )
      .expected(exactly(
      ))
    )

TEST_GENERATION(test_03,
    Generation::TestCase()
      .input(    clause({ selected(f2(a,b) == a),  f2(b,c) == a  }) )
      .expected(exactly(
            clause({ a != a, f2(a,b) == a, a != b, b != c  })
      ))
    )

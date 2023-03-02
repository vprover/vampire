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


REGISTER_GEN_TESTER(DelayedFactoring, testOrdering(), env.options)

#define MY_SYNTAX_SUGAR                                                                   \
  DECL_DEFAULT_VARS                                                                       \
  DECL_SORT(s)                                                                            \
  DECL_CONST(a, s)                                                                        \
  DECL_CONST(b, s)                                                                        \
  DECL_CONST(c, s)                                                                        \
  DECL_FUNC(f, {s}, s)                                                                    \
  DECL_FUNC(g, {s}, s)                                                                    \
  DECL_FUNC(f2, {s,s}, s)                                                                 \
  DECL_FUNC(g2, {s,s}, s)                                                                 \
  DECL_PRED(P, {s})                                                                       \
  DECL_PRED(Q, {s})                                                                       \
  DECL_PRED(P3, {s,s,s,})                                                                 \

TEST_GENERATION(test_01,
    Generation::TestCase()
      .input(    clause({ selected(P(x)), selected(P(a))  }) )
      .expected(exactly(
            clause({ P(a), a != x  })
      ))
    )

TEST_GENERATION(test_02,
    Generation::TestCase()
      .input(    clause({ selected(P(x)), P(a)  }) )
      .expected(exactly(
      ))
    )

TEST_GENERATION(test_03,
    Generation::TestCase()
      .input(    clause({ selected(Q(x)), selected(P(a))  }) )
      .expected(exactly(
      ))
    )


TEST_GENERATION(test_04,
    Generation::TestCase()
      .input(    clause({ selected(P(x)), selected(P(b)), selected(P(a))  }) )
      .expected(exactly(
            clause({ P(a), a != x , P(b) })
          , clause({ P(a), a != b , P(x) })
          , clause({ P(b), x != b , P(a) })
      ))
    )


TEST_GENERATION(test_05,
    Generation::TestCase()
      .input(    clause({ selected(~P(x)), selected(~P(b)), selected(~P(a))  }) )
      .expected(exactly(
      ))
    )

TEST_GENERATION(test_06,
    Generation::TestCase()
      .input(    clause({ selected(P3(x,b,c)), selected(P3(a,y,c))  }) )
      .expected(exactly(
            clause({ P3(x,b,c), x != a, b != y, c != c  })
      ))
    )

TEST_GENERATION(test_07,
    Generation::TestCase()
      .input(    clause({ selected(P(b)), selected(P(b))  }) )
      .expected(exactly(
            clause({ P(b)  })
      ))
    )

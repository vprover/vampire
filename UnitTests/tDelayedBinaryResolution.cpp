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
#include "Indexing/FingerprintIndex.hpp"
#include "Kernel/KBO.hpp"

using namespace Test;
using namespace Test::Generation;

inline Ordering* testOrdering(){
  static Ordering* ord = KBO::newPlainKBO();
  return ord;
}
Stack<Index*> delayedBinaryResIndices()
{ auto brIndex = new LiteralFingerprintIndex("BinaryResIndex");
  return {
    new DelayedNonEquations(brIndex),
  }; }


REGISTER_GEN_TESTER(DelayedBinaryResolution)

#define MY_SYNTAX_SUGAR                                                                             \
  DECL_DEFAULT_VARS                                                                                 \
  DECL_VAR(x0, 0)                                                                                   \
  DECL_VAR(x1, 1)                                                                                   \
  DECL_VAR(x2, 2)                                                                                   \
  DECL_VAR(x3, 3)                                                                                   \
  DECL_SORT(s)                                                                                      \
  DECL_CONST(a, s)                                                                                  \
  DECL_CONST(b, s)                                                                                  \
  DECL_CONST(c, s)                                                                                  \
  DECL_FUNC(f, {s}, s)                                                                              \
  DECL_FUNC(g, {s}, s)                                                                              \
  DECL_FUNC(f2, {s,s}, s)                                                                           \
  DECL_FUNC(g2, {s,s}, s)                                                                           \
  DECL_PRED(P, {s})                                                                                 \
  DECL_PRED(Q, {s})                                                                                 \

TEST_GENERATION(test_01,
    Generation::TestCase()
      .indices(delayedBinaryResIndices())
      .input(    clause({ selected(P(a))  }) )
      .context({ clause({ selected(~P(b)) }) })
      .expected(exactly(
            clause({   })
      ))
    )

TEST_GENERATION(test_02,
    Generation::TestCase()
      .indices(delayedBinaryResIndices())
      .input(    clause({ selected(P(x0))  }) )
      .context({ clause({ selected(~P(b)) }) })
      .expected(exactly(
            clause({ x0 != b  })
      ))
    )

TEST_GENERATION(test_03,
    Generation::TestCase()
      .indices(delayedBinaryResIndices())
      .input(    clause({ selected(P(x0))  }) )
      .context({ clause({ selected(~P(x1)) }) })
      .expected(exactly(
            clause({ x0.sort(s) != x1  })
      ))
    )

TEST_GENERATION(test_04,
    Generation::TestCase()
      .indices(delayedBinaryResIndices())
      .input(    clause({ selected(P(a)), Q(b)  }) )
      .context({ clause({ selected(~P(a)) }) })
      .expected(exactly(
            clause({ a != a, Q(b) })
      ))
    )

TEST_GENERATION(test_05,
    Generation::TestCase()
      .indices(delayedBinaryResIndices())
      .input(    clause({ selected(P(a)), Q(b)  }) )
      .context({ clause({ selected(~P(a)), f(a) == c }) })
      .expected(exactly(
            clause({ a != a, Q(b), f(a) == c })
      ))
    )
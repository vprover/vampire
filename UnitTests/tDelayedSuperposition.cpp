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

inline Ordering* testOrdering(){
  static Ordering* ord = KBO::newPlainKBO();
  return ord;
}
Stack<Index*> delayedSuperpositionIndices()
{ return {
    new DelayedSubterms(*testOrdering()),
    new DelayedLHS(*testOrdering(), *env.options),
  }; }


REGISTER_GEN_TESTER(DelayedSuperposition, testOrdering(), env.options)

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

TEST_GENERATION(test_01,
    Generation::TestCase()
      .indices(delayedSuperpositionIndices())
      .input(    clause({ selected(f(a) == b)  }) )
      .context({ clause({ selected(g(f(c)) == c) }) })
      .expected(exactly(
            clause({ g(b) == c, a != c  })
      ))
    )

TEST_GENERATION(test_02,
    Generation::TestCase()
      .indices(delayedSuperpositionIndices())
      .input(    clause({ selected(f2(a,b) == b)  }) )
      .context({ clause({ selected(g(f2(c,a)) == c) }) })
      .expected(exactly(
            clause({ g(b) == c, a != c, b != a  })
      ))
    )


TEST_GENERATION(test_03_eq,
    Generation::TestCase()
      .indices(delayedSuperpositionIndices())
      .input(    clause({ selected(x == a)  }) )
      .context({ clause({ selected(g(f2(c,b)) == f(a)) }) })
      .expected(exactly(
            clause({ a == f(a) })
          , clause({ g(a) == f(a) })
          , clause({ g(f2(a,b)) == f(a) })
          , clause({ g(f2(c,a)) == f(a) })
      ))
    )

TEST_GENERATION(test_03_neq,
    Generation::TestCase()
      .indices(delayedSuperpositionIndices())
      .input(    clause({ selected(x == a)  }) )
      .context({ clause({ selected(g(f2(c,b)) != f(a)) }) })
      .expected(exactly(
            clause({ a != f(a) })
          , clause({ g(a) != f(a) })
          , clause({ g(f2(a,b)) != f(a) })
          , clause({ g(f2(c,a)) != f(a) })
      ))
    )


TEST_GENERATION(test_03_pos,
    Generation::TestCase()
      .indices(delayedSuperpositionIndices())
      .input(    clause({ selected(x == a)  }) )
      .context({ clause({ selected(P(g(f2(c,b)))) }) })
      .expected(exactly(
            clause({ P(a) })
          , clause({ P(g(a)) })
          , clause({ P(g(f2(a,b))) })
          , clause({ P(g(f2(c,a))) })
      ))
    )

TEST_GENERATION(test_03_neg,
    Generation::TestCase()
      .indices(delayedSuperpositionIndices())
      .input(    clause({ selected(x == a)  }) )
      .context({ clause({ selected(~P(g(f2(c,b)))) }) })
      .expected(exactly(
            clause({ ~P(a) })
          , clause({ ~P(g(a)) })
          , clause({ ~P(g(f2(a,b))) })
          , clause({ ~P(g(f2(c,a))) })
      ))
    )


TEST_GENERATION(test_varbanks_01,
    Generation::TestCase()
      .indices(delayedSuperpositionIndices())
      .input(    clause({ selected(f2(x,y) == a)  }) )
      .context({ clause({ selected(P(f2(x,y))) }) })
      .expected(exactly(
            clause({ P(a), x0 != x2.sort(s), x1 != x3.sort(s)  })
      ))
    )


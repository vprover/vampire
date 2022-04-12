/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */


#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Test/TestUtils.hpp"
#include "Test/GenerationTester.hpp"

#include "Indexing/TermIndex.hpp"
#include "Indexing/CodeTreeInterfaces.hpp"
#include "Inferences/InductionHypothesisRewriting.hpp"

using namespace Test;
using namespace Test::Generation;
using namespace Indexing;

Index* lhsIndex() {
  return new InductionEqualityLHSIndex(new CodeTreeTIS());
}

Index* subtermIndex() {
  return new InductionInequalitySubtermIndex(new TermSubstitutionTree(false));
}

class MockInduction
  : public GeneratingInferenceEngine
{
  ClauseIterator generateClauses(Clause* premise) override {
    return pvi(getSingletonIterator(premise));
  }
};

class GenerationTesterInductionHRW
  : public GenerationTester<InductionHypothesisRewriting>
{
public:
  GenerationTesterInductionHRW()
    : GenerationTester<InductionHypothesisRewriting>()
  {
    _rule.setInduction(new MockInduction);
  }
};

#define TEST_GENERATION_INDUCTION_HRW(name, ...)                                                              \
  TEST_FUN(name) {                                                                                            \
    GenerationTesterInductionHRW tester;                                                                      \
    __ALLOW_UNUSED(MY_SYNTAX_SUGAR)                                                                           \
    auto test = __VA_ARGS__;                                                                                  \
    test.run(tester);                                                                                         \
  }                                                                                                           \

/**
 * NECESSARY: We neet to tell the tester which syntax sugar to import for creating terms & clauses. 
 * See Test/SyntaxSugar.hpp for which kinds of syntax sugar are available
 */
#define MY_SYNTAX_SUGAR                                                                    \
  DECL_DEFAULT_VARS                                                                        \
  DECL_SORT(s)                                                                             \
  DECL_SKOLEM_CONST(sk1, s)                                                                \
  DECL_SKOLEM_CONST(sk2, s)                                                                \
  DECL_SKOLEM_CONST(sk3, s)                                                                \
  DECL_SKOLEM_CONST(sk4, s)                                                                \
  DECL_CONST(b, s)                                                                         \
  DECL_CONST(c, s)                                                                         \
  DECL_CONST(d, s)                                                                         \
  DECL_FUNC(r, {s}, s)                                                                     \
  DECL_TERM_ALGEBRA(s, {b, r})                                                             \
  DECL_FUNC(f, {s, s}, s)                                                                  \
  DECL_FUNC(g, {s}, s)                                                                     \
  DECL_PRED(p, {s})                                                                        \

// only one side is rewritten
TEST_GENERATION_INDUCTION_HRW(test_01,
    Generation::TestCase()
      .context({ fromInduction(clause({ sk1 == sk2 })) })
      .indices({ lhsIndex(), subtermIndex() })
      .input( fromInduction(clause({  sk2 != f(f(sk2,sk2), sk1) })) )
      .expected({
              clause({  sk1 != f(f(sk2,sk2), sk1) }),
              clause({  sk2 != f(f(sk1,sk1), sk1) }),
              clause({  sk2 != f(f(sk2,sk2), sk2) }),
      })
    )

// induction skolems are used only once
TEST_GENERATION_INDUCTION_HRW(test_02,
    Generation::TestCase()
      .context({
        fromInduction(clause({ f(sk1,sk4) == b })),
        fromInduction(clause({ f(sk2,sk3) == b })),
        fromInduction(clause({ sk2 == sk4 }))
      })
      .indices({ lhsIndex(), subtermIndex() })
      .input( fromInduction(clause({ f(sk1,sk4) != f(sk2,sk3) })) )
      .expected({
        clause({ b != f(sk2,sk3) }), // result clause used again
        clause({ b != b }),
        clause({ f(sk2,sk3) != f(sk2,sk3) }),

        clause({ f(sk1,sk4) != b }), // result clause used again
        clause({ b != b }),
        clause({ f(sk1,sk4) != f(sk1,sk4) }),

        clause({ f(sk1,sk2) != f(sk2,sk3) }),
        clause({ f(sk1,sk4) != f(sk4,sk3) })
      })
    )

// cases where nothing happens
TEST_GENERATION_INDUCTION_HRW(test_03,
    Generation::TestCase()
      .context({
        fromInduction(clause({ sk1 != sk2 })), // due to same polarity
        fromInduction(clause({ sk2 == sk4 }))  // due to sk4
      })
      .indices({ lhsIndex(), subtermIndex() })
      .input( fromInduction(clause({ sk1 != f(sk2,sk1) })) )
      .expected(none())
    )

// symmetric case for polarity exclusion above
TEST_GENERATION_INDUCTION_HRW(test_04,
    Generation::TestCase()
      .context({
        fromInduction(clause({ sk2 != sk3 })), // due to sk3
        fromInduction(clause({ sk1 == sk2 }))  // due to same polarity
      })
      .indices({ lhsIndex(), subtermIndex() })
      .input( fromInduction(clause({ sk1 == f(sk2,sk1) })) )
      .expected(none())
    )

// only same literal is recursed upon
TEST_GENERATION_INDUCTION_HRW(test_05,
    Generation::TestCase()
      .context({
        fromInduction(clause({ sk1 == b })),
        fromInduction(clause({ sk2 == d }))
      })
      .indices({ lhsIndex(), subtermIndex() })
      .input( fromInduction(clause({ c != f(sk2,sk1), c != f(sk1,sk2) })) )
      .expected({
        clause({ c != f(d,sk1), c != f(sk1,sk2) }), // result clause used again
        clause({ c != f(d,b), c != f(sk1,sk2) }),

        clause({ c != f(sk2,b), c != f(sk1,sk2) }), // result clause used again
        clause({ c != f(d,b), c != f(sk1,sk2) }),

        clause({ c != f(sk2,sk1), c != f(b,sk2) }), // result clause used again
        clause({ c != f(sk2,sk1), c != f(b,d) }),

        clause({ c != f(sk2,sk1), c != f(sk1,d) }), // result clause used again
        clause({ c != f(sk2,sk1), c != f(b,d) })
      })
    )

// multiple literals
TEST_GENERATION_INDUCTION_HRW(test_06,
    Generation::TestCase()
      .context({
        fromInduction(clause({ sk1 == b, p(c) }))
      })
      .indices({ lhsIndex(), subtermIndex() })
      .input( fromInduction(clause({ sk1 != b, p(d) })) )
      .expected({
        clause({ b != b, p(c), p(d) }),
        clause({ sk1 != sk1, p(c), p(d) })
      })
    )

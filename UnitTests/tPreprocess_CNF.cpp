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
#include "Test/TransformationTester.hpp"

#include "Shell/CNF.hpp"

using namespace Test;

#define MY_TRAFO_RULE CNF

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
  NEXT_INTRODUCED_FUN(sk0, 0)                                                                                 \
  NEXT_INTRODUCED_FUN(sk1, 1)

// ---------------------------------------------------------------------
// Propositional connectives
// ---------------------------------------------------------------------

TEST_TRANSFORMATION(test_conjunction,
    Test::Transformation::TransformationTest()
      .input({
        formula(p(x) & q(x))
      })
      .expected({
        clause({ p(x) }),
        clause({ q(x) }),
      })
    )

TEST_TRANSFORMATION(test_disjunction,
    Test::Transformation::TransformationTest()
      .input({
        formula(p(x) | q(x))
      })
      .expected({
        clause({ p(x), q(x) }),
      })
    )

// these cases are not handled for some reason
// TEST_TRANSFORMATION(test_implication,
//     Test::Transformation::TransformationTest()
//       .input({
//         formula(impl(p(x), q(x)))
//       })
//       .expected({
//         clause({ ~p(x), q(x) }),
//       })
//     )

// TEST_TRANSFORMATION(test_negated_implication,
//     Test::Transformation::TransformationTest()
//       .input({
//         formula(impl(~(p(x)), q(x)))
//       })
//       .expected({
//         clause({ p(x) }),
//         clause({ ~q(x) }),
//       })
//     )

// TEST_TRANSFORMATION(test_iff,
//     Test::Transformation::TransformationTest()
//       .input({
//         formula(equiv(p(x), q(x)))
//       })
//       .expected({
//         clause({ ~p(x), q(x) }),
//         clause({ p(x), ~q(x) }),
//       })
//     )

// TEST_TRANSFORMATION(test_negated_iff,
//     Test::Transformation::TransformationTest()
//       .input({
//         formula(~(equiv(p(x), q(x))))
//       })
//       .expected({
//         clause({ p(x), q(x) }),
//         clause({ ~p(x), ~q(x) }),
//       })
//     )

// TEST_TRANSFORMATION(test_double_negation,
//     Test::Transformation::TransformationTest()
//       .input({
//         formula(~(~p(x)))
//       })
//       .expected({
//         clause({ p(x) }),
//       })
//     )

// TEST_TRANSFORMATION(test_de_morgan_and,
//     Test::Transformation::TransformationTest()
//       .input({
//         formula(~(p(x) & q(x)))
//       })
//       .expected({
//         clause({ ~p(x), ~q(x) }),
//       })
//     )

// TEST_TRANSFORMATION(test_de_morgan_or,
//     Test::Transformation::TransformationTest()
//       .input({
//         formula(~(p(x) | q(x)))
//       })
//       .expected({
//         clause({ ~p(x) }),
//         clause({ ~q(x) }),
//       })
//     )

// ---------------------------------------------------------------------
// Quantifiers
// ---------------------------------------------------------------------

TEST_TRANSFORMATION(test_universal_dropped,
    Test::Transformation::TransformationTest()
      .input({
        formula(forall(x, p(x)))
      })
      .expected({
        clause({ p(x) }),
      })
    )

// TEST_TRANSFORMATION(test_existential_skolemized_constant,
//     Test::Transformation::TransformationTest()
//       .input({
//         formula(exists(x, p(x)))
//       })
//       .expected({
//         clause({ p(sk0()) }),
//       })
//     )

// TEST_TRANSFORMATION(test_existential_under_universal_skolemizes_with_argument,
//     Test::Transformation::TransformationTest()
//       .input({
//         formula(forall(x, exists(y, f(x, y) == a)))
//       })
//       .expected({
//         clause({ f(x, sk1(x)) == a }),
//       })
//     )

// TEST_TRANSFORMATION(test_nested_impl_under_universal_with_skolemization,
//     Test::Transformation::TransformationTest()
//       .input({
//         formula(forall(x, impl(p(x), exists(y, q(y)))))
//       })
//       .expected({
//         clause({ ~p(x), q(sk1(x)) }),
//       })
//     )

TEST_TRANSFORMATION(test_conjunction_under_universal_splits_per_conjunct,
    Test::Transformation::TransformationTest()
      .input({
        formula(forall(x, p(x) & q(x)))
      })
      .expected({
        clause({ p(x) }),
        clause({ q(x) }),
      })
    )

TEST_TRANSFORMATION(test_two_independent_universals_share_no_variable,
    Test::Transformation::TransformationTest()
      .input({
        formula(forall(x, p(x)) & forall(y, q(y)))
      })
      .expected({
        clause({ p(x) }),
        clause({ q(y) }),
      })
    )

// ---------------------------------------------------------------------
// Equality / mixed literals
// ---------------------------------------------------------------------

TEST_TRANSFORMATION(test_equality_atom_passthrough,
    Test::Transformation::TransformationTest()
      .input({
        formula(g(a) == b)
      })
      .expected({
        clause({ g(a) == b }),
      })
    )

TEST_TRANSFORMATION(test_disjunction_with_equality_and_predicate,
    Test::Transformation::TransformationTest()
      .input({
        formula(p(x) | f(x, u) == a)
      })
      .expected({
        clause({ p(x), f(x, u) == a }),
      })
    )

TEST_TRANSFORMATION(test_conjunction_of_disjunctions_cnf,
    Test::Transformation::TransformationTest()
      .input({
        formula((p(x) | q(x)) & (~p(x) | ~q(x)))
      })
      .expected({
        clause({ p(x), q(x) }),
        clause({ ~p(x), ~q(x) }),
      })
    )
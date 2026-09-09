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

#include "Shell/Rectify.hpp"

using namespace Test;

#define MY_TRAFO_RULE Rectify

#define MY_SYNTAX_SUGAR                                                                                       \
  DECL_SORT(s)                                                                                                \
  DECL_VAR_SORTED(x, 0, s)                                                                                    \
  DECL_VAR_SORTED(y, 1, s)                                                                                    \
  DECL_VAR_SORTED(z, 2, s)                                                                                    \
  DECL_FUNC(f, {s, s}, s)                                                                                     \
  DECL_FUNC(g, {s}, s)                                                                                        \
  DECL_CONST(a, s)                                                                                            \
  DECL_CONST(b, s)                                                                                            \
  DECL_PRED (p, {s})                                                                                          \
  DECL_PRED (q, {s})                                                                                          \

// ---------------------------------------------------------------------
// Already-rectified formulas: identity
// ---------------------------------------------------------------------

TEST_TRANSFORMATION(test_no_quantifiers_is_identity,
    Test::Transformation::TransformationTest()
      .input({
        formula(forall(x, forall(y, p(x) & q(y))))
      })
      .expected({
        formula(forall(x, forall(y, p(x) & q(y))))
      })
    )

TEST_TRANSFORMATION(test_single_clean_quantifier_is_identity,
    Test::Transformation::TransformationTest()
      .input({
        formula(forall(x, p(x)))
      })
      .expected({
        formula(forall(x, p(x)))
      })
    )

TEST_TRANSFORMATION(test_distinct_nested_names_is_identity,
    Test::Transformation::TransformationTest()
      .input({
        formula(forall(x, exists(y, f(x, y) == a)))
      })
      .expected({
        formula(forall(x, exists(y, f(x, y) == a)))
      })
    )

// ---------------------------------------------------------------------
// Shadowing: an inner binder reuses an outer binder's name
// ---------------------------------------------------------------------

TEST_TRANSFORMATION(test_inner_binder_shadows_outer_binder,
    Test::Transformation::TransformationTest()
      .input({
        formula(forall(x, p(x) & exists(x, q(x))))
      })
      .expected({
        formula(forall(x, p(x) & exists(y, q(y))))
      })
    )

TEST_TRANSFORMATION(test_three_deep_reuse_of_same_name,
    Test::Transformation::TransformationTest()
      .input({
        formula(forall(x, exists(x, forall(x, p(x)))))
      })
      .expected({
        // the innermost `p(x)` is bound by the innermost binder; once
        // un-shadowed, each of the three same-named binders needs its own name
        formula(forall(z, p(z)))
      })
    )

TEST_TRANSFORMATION(test_shadow_reused_in_multiple_positions_stays_consistent,
    Test::Transformation::TransformationTest()
      .input({
        formula(forall(x, exists(x, f(x, x) == a)))
      })
      .expected({
        // both occurrences of the shadowed `x` in `f(x,x)` refer to the same
        // (inner) binder, so both must be renamed to the same fresh variable
        formula(exists(y, f(y, y) == a))
      })
    )

// ---------------------------------------------------------------------
// Capture: a bound name coincides with a genuinely free occurrence
// ---------------------------------------------------------------------

TEST_TRANSFORMATION(test_bound_name_would_capture_free_occurrence,
    Test::Transformation::TransformationTest()
      .input({
        formula(forall(x, p(x) & exists(x, q(x))))
      })
      .expected({
        // `x` is free in the left conjunct; the `∃x` on the right must not
        // capture it, so the bound occurrence is renamed
        formula(forall(x, p(x) & exists(y, q(y))))
      })
    )

TEST_TRANSFORMATION(test_free_var_untouched_when_no_capture_risk,
    Test::Transformation::TransformationTest()
      .input({
        formula(forall(x, p(x) | forall(y, q(y))))
      })
      .expected({
        formula(p(x) | forall(y, q(y)))
      })
    )

// ---------------------------------------------------------------------
// Independent (non-nested) binders reusing the same name
// ---------------------------------------------------------------------

TEST_TRANSFORMATION(test_sibling_binders_reusing_same_name,
    Test::Transformation::TransformationTest()
      .input({
        formula(forall(x, p(x)) | exists(x, q(x)))
      })
      .expected({
        // `x` here names two unrelated binders; even though neither
        // literally shadows the other, rectification gives them distinct
        // names so each bound variable denotes exactly one binder formula-wide
        formula(forall(y, p(y)) | exists(x, q(x)))
      })
    )

TEST_TRANSFORMATION(test_sibling_binders_across_conjunction_with_function,
    Test::Transformation::TransformationTest()
      .input({
        formula(forall(x, f(x, a) == b) & forall(x, p(x)))
      })
      .expected({
        formula(forall(y, f(y, a) == b) & forall(x, p(x)))
      })
    )

// ---------------------------------------------------------------------
// Multiple nested renamings in one formula
// ---------------------------------------------------------------------

TEST_TRANSFORMATION(test_multiple_shadows_get_distinct_fresh_names,
    Test::Transformation::TransformationTest()
      .input({
        formula(forall(x, impl(p(x), exists(x, q(x) & exists(x, f(x, x) == a)))))
      })
      .expected({
        formula(forall(x, impl(p(x), exists(y, q(y) & exists(z, f(z, z) == a)))))
      })
    )

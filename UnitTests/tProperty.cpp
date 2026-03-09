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

#include "Shell/Property.hpp"

using namespace Shell;

/**
 * NECESSARY: We need to tell the tester which syntax sugar to import for creating terms & clauses.
 * See Test/SyntaxSugar.hpp for which kinds of syntax sugar are available
 */
#define MY_SYNTAX_SUGAR                                                                    \
  DECL_DEFAULT_VARS                                                                        \
  DECL_SORT(s)                                                                             \
  DECL_FUNC(f, {s}, s)                                                                     \
  DECL_CONST(c, s)                                                                         \
  DECL_PRED(p, {s})                                                                        \

// ==================== hasXEqualsY(const Formula*) tests ====================

// Group 1: LITERAL branch coverage

TEST_FUN(hasXEqualsY_positive_equality) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);
  ASS(Property::hasXEqualsY(atom(sorted(x, s) == y)));
}

TEST_FUN(hasXEqualsY_negative_equality) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);
  ASS(!Property::hasXEqualsY(atom(sorted(x, s) != y)));
}

TEST_FUN(hasXEqualsY_same_variable) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);
  ASS(!Property::hasXEqualsY(atom(sorted(x, s) == x)));
}

TEST_FUN(hasXEqualsY_first_arg_not_var) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);
  ASS(!Property::hasXEqualsY(atom(f(c) == y)));
}

TEST_FUN(hasXEqualsY_second_arg_not_var) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);
  ASS(!Property::hasXEqualsY(atom(sorted(x, s) == f(c))));
}

TEST_FUN(hasXEqualsY_non_equality) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);
  ASS(!Property::hasXEqualsY(atom(p(x))));
}

// Group 2: Connective polarity tracking

TEST_FUN(hasXEqualsY_double_negation) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);
  ASS(Property::hasXEqualsY(neg(neg(atom(sorted(x, s) == y)))));
}

TEST_FUN(hasXEqualsY_single_negation) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);
  ASS(!Property::hasXEqualsY(neg(atom(sorted(x, s) == y))));
}

TEST_FUN(hasXEqualsY_negated_inequality) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);
  // ~(x != y) => pol flipped by NOT to -1, then flipped by negative literal to 1
  ASS(Property::hasXEqualsY(neg(atom(sorted(x, s) != y))));
}

TEST_FUN(hasXEqualsY_conjunction) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);
  ASS(Property::hasXEqualsY(andf({atom(sorted(x, s) == y), atom(p(x))})));
}

TEST_FUN(hasXEqualsY_disjunction_no_match) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);
  ASS(!Property::hasXEqualsY(orf({atom(p(x)), atom(p(y))})));
}

TEST_FUN(hasXEqualsY_imp_left) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);
  // (x=y) => p(x): left side has negated polarity
  ASS(!Property::hasXEqualsY(imp(atom(sorted(x, s) == y), atom(p(x)))));
}

TEST_FUN(hasXEqualsY_imp_right) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);
  // p(x) => (x=y): right side keeps polarity
  ASS(Property::hasXEqualsY(imp(atom(p(x)), atom(sorted(x, s) == y))));
}

TEST_FUN(hasXEqualsY_iff) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);
  // (x=y) <=> p(x): both sides get polarity 0, 0>=0 passes
  ASS(Property::hasXEqualsY(iff(atom(sorted(x, s) == y), atom(p(x)))));
}

TEST_FUN(hasXEqualsY_xor) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);
  // (x=y) XOR p(x): same as IFF, polarity 0
  ASS(Property::hasXEqualsY(xorf(atom(sorted(x, s) == y), atom(p(x)))));
}

TEST_FUN(hasXEqualsY_iff_negative_literal) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);
  // (x!=y) <=> p(x): pol=0, negative literal flips to -0=0, still >=0
  ASS(Property::hasXEqualsY(iff(atom(sorted(x, s) != y), atom(p(x)))));
}

// Group 3: Quantifier variable tracking

TEST_FUN(hasXEqualsY_forall_positive) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);
  ASS(Property::hasXEqualsY(forall({x, y}, s, atom(sorted(x, s) == y))));
}

TEST_FUN(hasXEqualsY_exists_positive) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);
  // exists marks vars existential, so x=y cannot match
  ASS(!Property::hasXEqualsY(exists({x, y}, s, atom(sorted(x, s) == y))));
}

TEST_FUN(hasXEqualsY_exists_forall_mixed) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);
  // exists x. forall y. (x = y): x is existential, blocks match
  ASS(!Property::hasXEqualsY(exists({x}, s, forall({y}, s, atom(sorted(x, s) == y)))));
}

TEST_FUN(hasXEqualsY_forall_one_var_free) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);
  // forall x. (x = y): y is free (universal by convention)
  ASS(Property::hasXEqualsY(forall({x}, s, atom(sorted(x, s) == y))));
}

// Group 4: Quantifiers + polarity interaction

TEST_FUN(hasXEqualsY_not_exists) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);
  // ~(exists x y. (x=y)): NOT flips pol to -1, EXISTS eff_pol=1 (no marking), but pol<0
  ASS(!Property::hasXEqualsY(neg(exists({x, y}, s, atom(sorted(x, s) == y)))));
}

TEST_FUN(hasXEqualsY_not_forall) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);
  // ~(forall x y. (x=y)): NOT flips pol to -1, FORALL eff_pol=-1 marks vars existential
  ASS(!Property::hasXEqualsY(neg(forall({x, y}, s, atom(sorted(x, s) == y)))));
}

TEST_FUN(hasXEqualsY_double_neg_exists) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);
  // ~~(exists x y. (x=y)): pol restored to 1, but EXISTS still marks vars existential
  ASS(!Property::hasXEqualsY(neg(neg(exists({x, y}, s, atom(sorted(x, s) == y))))));
}

// Group 5: Quantifier cleanup / scoping

TEST_FUN(hasXEqualsY_variable_shadowing) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);
  // exists x. forall x. (x = y): inner forall clears existential mark for x
  ASS(Property::hasXEqualsY(exists({x}, s, forall({x}, s, atom(sorted(x, s) == y)))));
}

TEST_FUN(hasXEqualsY_scoped_exists_conjunction) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);
  // (exists x. p(x)) /\ (x = y): exists scoped to left conjunct, cleanup restores x
  ASS(Property::hasXEqualsY(andf({exists({x}, s, atom(p(x))), atom(sorted(x, s) == y)})));
}

// Group 6: Combined connective + quantifier

TEST_FUN(hasXEqualsY_imp_exists_neg_literal) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);
  // (exists x y. (x != y)) => p(z): IMP left pol=-1, EXISTS eff_pol=1 (no marking),
  // neg literal flips pol from -1 to 1, both vars not existential => true
  ASS(Property::hasXEqualsY(imp(exists({x, y}, s, atom(sorted(x, s) != y)), atom(p(z)))));
}

TEST_FUN(hasXEqualsY_imp_forall_neg_context) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);
  // (forall x y. (x = y)) => p(z): IMP left pol=-1, FORALL eff_pol=-1 marks vars existential
  ASS(!Property::hasXEqualsY(imp(forall({x, y}, s, atom(sorted(x, s) == y)), atom(p(z)))));
}

// Group 7: Constant formulas

TEST_FUN(hasXEqualsY_true_formula) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);
  ASS(!Property::hasXEqualsY(trueF()));
}

TEST_FUN(hasXEqualsY_false_formula) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);
  ASS(!Property::hasXEqualsY(falseF()));
}

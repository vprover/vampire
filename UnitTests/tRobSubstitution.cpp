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
#include "Kernel/RobSubstitution.hpp"

using namespace Kernel;

void check(TermList t1, TermList t2) {
  RobSubstitution subs;
  ASS(subs.match(t1, 0, t2, 1))
}

TEST_FUN(test_match1) {
  DECL_DEFAULT_VARS
  DECL_SORT(s);
  DECL_FUNC(f, {s, s}, s);
  DECL_CONST(a, s)
  DECL_CONST(b, s)
  check(f(f(a, y), f(x, b)), f(f(a,b),f(a,b)));

}

/*
 * Syntactic unification inside lambda bodies (what -uwa off relies on in higher-order logic).
 * Lambdas are decomposed like any other term, but an ordinary variable must never be bound to a
 * term with a loose de Bruijn index: it stands for a term outside the binder.
 */

#define HOL_SUGAR                                \
  DECL_SORT(srt)                                 \
  DECL_VAR_SORTED(x, 0, srt)                     \
  DECL_CONST(a, srt)                             \
  DECL_CONST(f, arrow(srt, srt))           \
  DECL_CONST(f2, arrow({srt, srt}, srt))   \
  DECL_DE_BRUIJN_INDEX(db0, 0, srt)

// ^y. x  =?  ^y. a   with   x -> a
TEST_FUN(unify_under_lambda_constant_body) {
  HOL_SUGAR
  RobSubstitution subs;
  ASS(subs.unify(lam(srt, x), 0, lam(srt, a), 1))
  ASS_EQ(subs.apply(TermList(x), 0), TermList(a))
}

// ^y. f x  =?  ^y. f a   with   x -> a
TEST_FUN(unify_under_lambda_rigid_body) {
  HOL_SUGAR
  RobSubstitution subs;
  ASS(subs.unify(lam(srt, ap(f, x)), 0, lam(srt, ap(f, a)), 1))
  ASS_EQ(subs.apply(TermList(x), 0), TermList(a))
}

// ^y. f2 y x  =?  ^y. f2 y a   with   x -> a: the bound variable lines up with itself
TEST_FUN(unify_under_lambda_bound_variable_kept) {
  HOL_SUGAR
  RobSubstitution subs;
  ASS(subs.unify(lam(srt, ap(ap(f2, db0), x)), 0,
                 lam(srt, ap(ap(f2, db0), a)), 1))
  ASS_EQ(subs.apply(TermList(x), 0), TermList(a))
}

// ^y. x  =?  ^y. y   has no unifier: x cannot capture the bound variable
TEST_FUN(unify_under_lambda_no_escape_bare) {
  HOL_SUGAR
  RobSubstitution subs;
  ASS(!subs.unify(lam(srt, x), 0, lam(srt, db0), 1))
}

// ^y. f x  =?  ^y. f y   has no unifier either
TEST_FUN(unify_under_lambda_no_escape_nested) {
  HOL_SUGAR
  RobSubstitution subs;
  ASS(!subs.unify(lam(srt, ap(f, x)), 0, lam(srt, ap(f, db0)), 1))
}

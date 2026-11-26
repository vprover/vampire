/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * Tests for Clause::foLikeWeight, the clause selection weight under -hol_fo_weight (hfw).
 */

#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"

#include "Kernel/Clause.hpp"

using namespace Test;

#define MY_SYNTAX_SUGAR                               \
  DECL_SORT(srt)                                      \
  DECL_SORT_VAR(alpha, 101)                           \
  DECL_VAR_SORTED(F, 1, arrow(srt, srt))              \
  DECL_VAR_SORTED(F2, 2, arrow({srt, srt}, srt))      \
  DECL_VAR_SORTED(G, 3, arrow(srt, srt))              \
  DECL_VAR_SORTED(H, 4, arrow(arrow(srt, srt), srt))  \
  DECL_CONST(a, srt)                                  \
  DECL_CONST(f, arrow(srt, srt))                      \
  DECL_CONST(f2, arrow({srt, srt}, srt))              \
  DECL_CONST(g, arrow(arrow(srt, srt), srt))          \
  DECL_POLY_CONST(pc, 1, alpha)                       \
  DECL_DE_BRUIJN_INDEX(db0, 0, srt)                   \
  DECL_DE_BRUIJN_INDEX(db0f, 0, arrow(srt, srt))

#define CHECK_WEIGHT(cl, w) \
  ASS_EQ((cl)->foLikeWeight(), w)

// f @ a: a rigid spine
TEST_FUN(rigid_unary)
{
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR)
  CHECK_WEIGHT(clause({ ap(f, a) == a }), 4)
}

// F @ a: a flex spine, its @ keeps counting
TEST_FUN(flex_unary)
{
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR)
  CHECK_WEIGHT(clause({ ap(F, a) == a }), 5)
}

// f2 @ a @ a vs F2 @ a @ a: the whole spine follows its head
TEST_FUN(binary_spines)
{
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR)
  CHECK_WEIGHT(clause({ ap(ap(f2, a), a) == a }), 5)
  CHECK_WEIGHT(clause({ ap(ap(F2, a), a) == a }), 7)
}

// f @ (F @ a): the outer spine is rigid, the inner one flex
TEST_FUN(flex_inside_rigid)
{
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR)
  CHECK_WEIGHT(clause({ ap(f, ap(F, a)) == a }), 6)
}

// g @ (^x. f @ x): lambda and de Bruijn index count 1 each, f's spine is rigid
TEST_FUN(lambda_rigid_body)
{
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR)
  CHECK_WEIGHT(clause({ ap(g, lam(srt, ap(f, db0))) == a }), 6)
}

// ^x. x @ a: a spine headed by a de Bruijn index is not rigid
TEST_FUN(de_bruijn_head)
{
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR)
  CHECK_WEIGHT(clause({ lam(arrow(srt, srt), ap(db0f, a)) == H }), 6)
}

// the type argument of a polymorphic symbol keeps counting, those of @ and of the equality do not
TEST_FUN(type_args)
{
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR)
  // pc(srt) = a: 1 (=) + 2 (pc, srt) + 1 (a)
  Clause* c1 = clause({ pc(srt) == a });
  ASS_EQ(c1->weight(), 4)
  CHECK_WEIGHT(c1, 4)

  // f @ pc(srt) = a: the @ node's sorts count only in the ordinary weight
  Clause* c2 = clause({ ap(f, pc(srt)) == a });
  ASS_EQ(c2->weight(), 8)
  CHECK_WEIGHT(c2, 5)

  // an equality at an arrow sort, also between two variables: its sort counts only in the ordinary weight
  Clause* c3 = clause({ f == F });
  ASS_EQ(c3->weight(), 5)
  CHECK_WEIGHT(c3, 3)
  Clause* c4 = clause({ F == G });
  ASS_EQ(c4->weight(), 5)
  CHECK_WEIGHT(c4, 3)
}

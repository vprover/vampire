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
 * Tests for the clause weight used for clause selection under -hol_selection_weight (hsw).
 */

#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"

#include "Kernel/Clause.hpp"
#include "Lib/Environment.hpp"
#include "Shell/Options.hpp"

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

/** the literal weight for clause selection of @b cl under -hol_selection_weight @b mode,
 * always computed by the custom traversal */
static unsigned selWeight(Clause* cl, const char* mode)
{
  env.options->set("hol_selection_weight", mode);
  unsigned w = cl->customLiteralWeightForClauseSelection(*env.options);
  env.options->set("hol_selection_weight", "off");
  return w;
}

#define CHECK_WEIGHTS(cl, wNoEncSorts, wFoLike)         \
  ASS_EQ(selWeight(cl, "no_enc_sorts"), wNoEncSorts)    \
  ASS_EQ(selWeight(cl, "fo_like"), wFoLike)

// with the option off, the traversal reproduces the ordinary weight
TEST_FUN(off_is_ordinary_weight)
{
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR)
  Stack<Clause*> cls = {
    clause({ ap(f, a) == a }),
    clause({ ap(F, a) == a }),
    clause({ ap(ap(f2, a), a) == a, ap(ap(F2, a), a) != a }),
    clause({ ap(f, ap(F, a)) == a }),
    clause({ ap(g, lam(srt, ap(f, db0))) == a }),
    clause({ lam(arrow(srt, srt), ap(db0f, a)) == H }),
    clause({ pc(srt) == a, ap(f, pc(srt)) != a }),
    clause({ f == F }),
    clause({ F == G }),
  };
  for (Clause* cl : cls) {
    ASS_EQ(selWeight(cl, "off"), cl->weight())
  }
}

// f @ a: a rigid spine
TEST_FUN(rigid_unary)
{
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR)
  CHECK_WEIGHTS(clause({ ap(f, a) == a }), 5, 4)
}

// F @ a: a flex spine, its @ keeps counting under fo_like
TEST_FUN(flex_unary)
{
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR)
  CHECK_WEIGHTS(clause({ ap(F, a) == a }), 5, 5)
}

// f2 @ a @ a vs F2 @ a @ a: the whole spine follows its head
TEST_FUN(binary_spines)
{
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR)
  CHECK_WEIGHTS(clause({ ap(ap(f2, a), a) == a }), 7, 5)
  CHECK_WEIGHTS(clause({ ap(ap(F2, a), a) == a }), 7, 7)
}

// f @ (F @ a): the outer spine is rigid, the inner one flex
TEST_FUN(flex_inside_rigid)
{
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR)
  CHECK_WEIGHTS(clause({ ap(f, ap(F, a)) == a }), 7, 6)
}

// g @ (^x. f @ x): lambda and de Bruijn index count 1 each, f's spine is rigid
TEST_FUN(lambda_rigid_body)
{
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR)
  CHECK_WEIGHTS(clause({ ap(g, lam(srt, ap(f, db0))) == a }), 8, 6)
}

// ^x. x @ a: a spine headed by a de Bruijn index is not rigid
TEST_FUN(de_bruijn_head)
{
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR)
  CHECK_WEIGHTS(clause({ lam(arrow(srt, srt), ap(db0f, a)) == H }), 6, 6)
}

// the type argument of a polymorphic symbol keeps counting, those of @ and of the equality do not
TEST_FUN(type_args)
{
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR)
  // pc(srt) = a: 1 (=) + 2 (pc, srt) + 1 (a)
  Clause* c1 = clause({ pc(srt) == a });
  ASS_EQ(selWeight(c1, "off"), 4)
  ASS_EQ(selWeight(c1, "no_enc_sorts"), 4)
  ASS_EQ(selWeight(c1, "fo_like"), 4)

  // f @ pc(srt) = a: the @ node's sorts count only under off
  Clause* c2 = clause({ ap(f, pc(srt)) == a });
  ASS_EQ(selWeight(c2, "off"), 8)
  ASS_EQ(selWeight(c2, "no_enc_sorts"), 6)
  ASS_EQ(selWeight(c2, "fo_like"), 5)

  // an equality at an arrow sort, also between two variables: its sort counts only under off
  Clause* c3 = clause({ f == F });
  ASS_EQ(selWeight(c3, "off"), 5)
  ASS_EQ(selWeight(c3, "no_enc_sorts"), 3)
  Clause* c4 = clause({ F == G });
  ASS_EQ(selWeight(c4, "off"), 5)
  ASS_EQ(selWeight(c4, "no_enc_sorts"), 3)
  ASS_EQ(selWeight(c4, "fo_like"), 3)
}

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

#include "Shell/FunctionDefinitionHandler.hpp"

using namespace Shell;
using std::get;
using std::pair;

#define MY_SYNTAX_SUGAR                                                                    \
  DECL_DEFAULT_VARS                                                                        \
  DECL_SORT(s)                                                                             \
  DECL_SORT(u)                                                                             \
  DECL_CONST(b, s)                                                                         \
  DECL_FUNC(r, {s}, s)                                                                     \
  DECL_FUN_DEF(def_s, r(x))                                                                \
  DECL_TERM_ALGEBRA(s, {b, r})                                                             \
  DECL_CONST(b1, u)                                                                        \
  DECL_FUN_DEF(def_u, b1())                                                                \
  DECL_CONST(b2, u)                                                                        \
  DECL_FUNC(r1, {s, u}, u)                                                                 \
  DECL_FUNC(r2, {u, s}, u)                                                                 \
  DECL_TERM_ALGEBRA(u, {b1, b2, r1, r2})                                                   \
  DECL_FUNC(f, {s, s}, s)                                                                  \
  DECL_FUNC(g, {s}, s)                                                                     \
  DECL_FUNC(h, {s, s, u}, u)                                                               \
  DECL_PRED(p, {s})                                                                        \
  DECL_PRED_DEF(def_p, p(x))                                                               \
  DECL_PRED(q, {u, s})                                                                     \
  DECL_PRED_DEF(def_q, q(x,y))

inline void addFunctionDefs(FunctionDefinitionHandler& handler, std::initializer_list<Clause*> cls) {
  auto ul = UnitList::empty();
  for (const auto& cl : cls) {
    UnitList::push(cl, ul);
  }
  Problem prb;
  prb.addUnits(ul);
  Options opts;
  opts.set("structural_induction_kind", "recursion");

  handler.initAndPreprocessLate(prb,opts);
}

inline void checkTemplateBranches(FunctionDefinitionHandler& handler, TermSugar t, const std::vector<pair<TermSugar, std::vector<TermSugar>>>& expected) {
  auto templ = handler.getRecursionTemplate(t.sugaredExpr().term());
  ASS(templ);
  auto actual = templ->branches();
  ASS_EQ(actual.size(), expected.size());
  for (unsigned i = 0; i < actual.size(); i++) {
    ASS_EQ(TermList(actual[i]._header), expected[i].first.sugaredExpr());
    auto r = actual[i]._recursiveCalls;
    ASS_EQ(r.size(), expected[i].second.size());
    for (unsigned j = 0; j < r.size(); j++) {
      ASS_EQ(TermList(r[j]), expected[i].second[j].sugaredExpr());
    }
  }
}

// not well-founded functions
TEST_FUN(test_01) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR)
  FunctionDefinitionHandler handler;
  addFunctionDefs(handler, {
    clause({ def_s(f(r(x), r(y)), f(f(x, r(r(y))), y)) }),
    clause({ def_s(g(r(x)), g(f(x,x))) }),
    clause({ def_u(h(x, y, r1(x, z)), h(y, y, z)) }),
    clause({ def_u(h(r(x), y, z), h(x, x, r2(y,z))) }),
    clause({ def_p(r(r(x))), p(y) }),
    clause({ def_q(r1(x,y),r(z)), q(y,r(z)), g(b) == b, ~q(z,b) }),
  });

  ASS(!handler.getRecursionTemplate(f(x,y).sugaredExpr().term()));
  ASS(!handler.getRecursionTemplate(g(x).sugaredExpr().term()));
  ASS(!handler.getRecursionTemplate(h(x,y,z).sugaredExpr().term()));
  ASS(!handler.getRecursionTemplate(p(x)));
  ASS(!handler.getRecursionTemplate(q(x,y)));
}

// not useful functions (either no recursive calls or no argument changes in any recursive call)
TEST_FUN(test_02) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR)
  FunctionDefinitionHandler handler;
  addFunctionDefs(handler, {
    clause({ def_s(f(x, r(y)), g(f(x, r(y)))) }),
    clause({ def_s(f(x, b), b) }),
    clause({ def_s(g(x), b) }),
  });

  ASS(!handler.getRecursionTemplate(f(x,y).sugaredExpr().term()));
  ASS(!handler.getRecursionTemplate(g(x).sugaredExpr().term()));
}

// adds missing cases
TEST_FUN(test_03) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR)
  FunctionDefinitionHandler handler;
  addFunctionDefs(handler, {
    clause({ def_s(f(r(x), r(y)), f(x,y)) }),
    clause({ def_s(f(x,b), b) }),

    clause({ def_s(g(r(r(x))), g(x)) }),

    clause({ def_u(h(b, x, y), b1) }),
    clause({ def_u(h(r(x), b, y), b2) }),
    clause({ def_u(h(r(x), b, r1(y,z)), h(x, b, z)) }),

    clause({ def_p(r(r(x))), ~p(x) }),
    clause({ def_p(b), f(b,b) == b }),

    clause({ def_q(y,r(r(x))), ~q(y,x) }),
    clause({ ~def_q(r2(r1(x,y),z),b) }),
  });

  checkTemplateBranches(handler, f(x,y), {
    { f(x,b),       { } },
    { f(r(x),r(y)), { f(x,y) } },
    { f(b,r(x)),   { } } // added
  });

  checkTemplateBranches(handler, g(x), {
    { g(r(r(x))),   { g(x) } },
    { g(b),         { } }, // added
    { g(r(b)),      { } }, // added
  });

  checkTemplateBranches(handler, h(x,y,z), {
    { h(r(x), b, r1(y,z)), { h(x, b, z) } },
    { h(r(x), b, y), { } },
    { h(b, x, y),    { } },
    { h(r(x), r(y), z), { } } // added
  });

  checkTemplateBranches(handler, p(x).wrapInTerm(), {
    { p(b).wrapInTerm(),       { } },
    { p(r(r(x))).wrapInTerm(), { p(x).wrapInTerm() } },
    { p(r(b)).wrapInTerm(),    { } } // added
  });

  checkTemplateBranches(handler, q(x,y).wrapInTerm(), {
    { q(r2(r1(x,y),z),b).wrapInTerm(),      { } },
    { q(y,r(r(x))).wrapInTerm(),            { q(y,x).wrapInTerm() } },
    { q(b1,b).wrapInTerm(),                 { } }, // added
    { q(b2,b).wrapInTerm(),                 { } }, // added
    { q(r1(x,y),b).wrapInTerm(),            { } }, // added
    { q(r2(b1,x),b).wrapInTerm(),           { } }, // added
    { q(r2(b2,x),b).wrapInTerm(),           { } }, // added
    { q(r2(r2(x,y),z),b).wrapInTerm(),      { } }, // added
    { q(x,r(b)).wrapInTerm(),               { } }  // added
  });
}

// correctly merges branches
TEST_FUN(test_04) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR)
  FunctionDefinitionHandler handler;
  addFunctionDefs(handler, {
    clause({ def_s(f(r(x), r(y)), f(x,y)) }),
    clause({ def_s(f(r(x),r(x)), f(x,x)) }),
    clause({ def_s(f(b,x), b) }),
    clause({ def_s(f(r(x),b), g(x)) }),

    clause({ def_s(g(r(r(x))), g(r(x))) }),
    clause({ def_s(g(r(r(x))), g(x)) }),
    clause({ def_s(g(r(b)), b) }),
    clause({ def_s(g(b), b) }),

    clause({ def_u(h(b, x, y), b1) }),
    clause({ def_u(h(r(x), y, z), h(x, y, z)) }),
    clause({ def_u(h(r(x), z, y), h(x, z, y)) }),

    clause({ def_p(r(r(x))), ~p(x) }),
    clause({ def_p(r(r(x))), ~p(r(x)) }),
    clause({ def_p(b) }),

    clause({ ~def_q(y,r(x)), ~q(y,x) }),
    clause({ ~def_q(y,b) }),
    clause({ def_q(z,r(b)), q(z,b) }),
  });

  checkTemplateBranches(handler, f(x,y), {
    { f(r(x),b),    { } },
    { f(b,x),       { } },
    { f(r(x),r(y)), { f(x,y) } },
  });

  checkTemplateBranches(handler, g(x), {
    { g(b),         { } },
    { g(r(b)),      { } },
    { g(r(r(x))),   { g(x) } },
    { g(r(r(x))),   { g(r(x)) } },
  });

  checkTemplateBranches(handler, h(x,y,z), {
    { h(r(x), z, y), { h(x, z, y) } },
    { h(b, x, y),    { } },
  });

  checkTemplateBranches(handler, p(x).wrapInTerm(), {
    { p(b).wrapInTerm(),       { } },
    { p(r(r(x))).wrapInTerm(), { p(r(x)).wrapInTerm() } },
    { p(r(r(x))).wrapInTerm(), { p(x).wrapInTerm() } },
    { p(r(b)).wrapInTerm(),    { } } // added
  });

  checkTemplateBranches(handler, q(x,y).wrapInTerm(), {
    { q(y,b).wrapInTerm(),    { } },
    { q(y,r(x)).wrapInTerm(), { q(y,x).wrapInTerm() } }
  });
}

// non-term-algebra sorts are ignored
TEST_FUN(test_05) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR)
  DECL_SORT(t)                     \
  DECL_FUNC(f1, {t}, t)            \
  DECL_PRED(p1, {t})               \
  DECL_FUN_DEF(defT, f1(x))        \
  DECL_PRED_DEF(def_p1, p1(x))     \

  FunctionDefinitionHandler handler;
  addFunctionDefs(handler, {
    clause({ defT(f1(f1(x)), f1(x)) }),
    clause({ def_p1(f1(x)), p1(x) }),
  });

  ASS(!handler.getRecursionTemplate(f1(x).sugaredExpr().term()));
  ASS(!handler.getRecursionTemplate((Literal*)p1(x)));
}

// headers with non-term-algebra arguments are not discarded
// but trivial headers are added to ensure well-definedness
TEST_FUN(test_06) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR)
  FunctionDefinitionHandler handler;
  addFunctionDefs(handler, {
    clause({ def_p(g(x)), p(x) }),
    clause({ def_s(f(r(x),g(y)), f(x,g(y))), }),
  });

  checkTemplateBranches(handler, p(x).wrapInTerm(), {
    { p(g(x)).wrapInTerm(), { p(x).wrapInTerm() } },
    { p(x).wrapInTerm(),    { } },
  });

  checkTemplateBranches(handler, f(x,y), {
    { f(r(x),g(y)), { f(x,g(y)) } },
    { f(x,y),       { } },
  });
}

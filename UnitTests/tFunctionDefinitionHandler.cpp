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

#include <tuple>

#include "Kernel/FormulaUnit.hpp"

#include "Shell/FunctionDefinitionHandler.hpp"

using namespace Shell;
using std::get;
using std::pair;

#define MY_SYNTAX_SUGAR                                                                    \
  DECL_DEFAULT_VARS                                                                        \
  DECL_VAR(x3, 3)                                                                          \
  DECL_VAR(x4, 4)                                                                          \
  DECL_VAR(x5, 5)                                                                          \
  DECL_VAR(x6, 6)                                                                          \
  DECL_VAR(x7, 7)                                                                          \
  DECL_VAR(x8, 8)                                                                          \
  DECL_VAR(x9, 9)                                                                          \
  DECL_VAR(x10, 10)                                                                        \
  DECL_VAR(x11, 11)                                                                        \
  DECL_SORT(s)                                                                             \
  DECL_DEF(def_s, s.sugaredExpr())                                                         \
  DECL_SORT(u)                                                                             \
  DECL_DEF(def_u, u.sugaredExpr())                                                         \
  DECL_CONST(b, s)                                                                         \
  DECL_FUNC(r, {s}, s)                                                                     \
  DECL_TERM_ALGEBRA(s, {b, r})                                                             \
  DECL_CONST(b1, u)                                                                        \
  DECL_CONST(b2, u)                                                                        \
  DECL_FUNC(r1, {s, u}, u)                                                                 \
  DECL_FUNC(r2, {u, s}, u)                                                                 \
  DECL_TERM_ALGEBRA(u, {b1, b2, r1, r2})                                                   \
  DECL_FUNC(f, {s, s}, s)                                                                  \
  DECL_FUNC(g, {s}, s)                                                                     \
  DECL_FUNC(h, {s, s, u}, u)                                                               \
  DECL_PRED(p, {s})                                                                        \
  DECL_PRED(q, {u, s})

inline void addFunctionDefs(FunctionDefinitionHandler& handler, std::initializer_list<Clause*> cls) {
  auto ul = UnitList::empty();
  for (const auto& cl : cls) {
    UnitList::push(cl, ul);
  }
  Problem prb;
  prb.addUnits(ul);

  handler.preprocess(prb);
}

inline void checkTemplateBranches(FunctionDefinitionHandler& handler, TermSugar t, const vvector<pair<TermSugar, vvector<TermSugar>>>& p) {
  auto templ = handler.getInductionTemplate(t.sugaredExpr().term());
  ASS(templ);
  auto b = templ->branches();
  ASS_EQ(b.size(), p.size());
  for (unsigned i = 0; i < b.size(); i++) {
    ASS_EQ(TermList(b[i]._header), p[i].first.sugaredExpr());
    auto r = b[i]._recursiveCalls;
    ASS_EQ(r.size(), p[i].second.size());
    for (unsigned j = 0; j < r.size(); j++) {
      ASS_EQ(TermList(r[j]), p[i].second[j].sugaredExpr());
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
    // clause({ def_s(p(r(r(x))).wrapInTerm(), /*unused*/b(), { p(y) } } },
    // { { q(r1(x,y),r(z)).wrapInTerm(), /*unused*/b(), { q(y,r(z)), g(b) == b, q(z,b) } } },
  });

  ASS(!handler.getInductionTemplate(f(x,y).sugaredExpr().term()));
  ASS(!handler.getInductionTemplate(g(x).sugaredExpr().term()));
  ASS(!handler.getInductionTemplate(h(x,y,z).sugaredExpr().term()));
  // ASS(!handler.getInductionTemplate(p));
  // ASS(!handler.getInductionTemplate(q));
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

  ASS(!handler.getInductionTemplate(f(x,y).sugaredExpr().term()));
  ASS(!handler.getInductionTemplate(g(x).sugaredExpr().term()));
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

    // { { p(r(r(x))).wrapInTerm(), /*unused*/b(), { ~p(x) } },
    //   { p(b).wrapInTerm(), /*unused*/b(), { f(b,b) == b } } },

    // { { q(y,r(r(x))).wrapInTerm(), /*unused*/b(), { ~q(y,x) } },
    //   { (~q(r2(r1(x,y),z),b)).wrapInTerm(), /*unused*/b(), { } } }
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

  // checkTemplateBranches(handler, p, {
  //   { p(r(r(x))), { p(x) } },
  //   { p(b),       { } },
  //   { p(r(b)),    { } } // added
  // });

  // checkTemplateBranches(handler, q, {
  //   { q(y,r(r(x))),            { q(y,x) } },
  //   { q(r2(r1(x,y),z),b),      { } },
  //   { q(b1,b),                 { } }, // added
  //   { q(b2,b),                 { } }, // added
  //   { q(r1(x4,x5),b),          { } }, // added
  //   { q(r2(b1,x7),b),          { } }, // added
  //   { q(r2(b2,x7),b),          { } }, // added
  //   { q(r2(r2(x10,x11),x7),b), { } }, // added
  //   { q(x,r(b)),               { } }  // added
  // });
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

    // { { p(r(r(x))).wrapInTerm(), /*unused*/b(), { ~p(x) } },
    //   { p(r(r(x))).wrapInTerm(), /*unused*/b(), { ~p(r(x)) } },
    //   { p(b).wrapInTerm(), /*unused*/b(), { } } },

    // { { (~q(y,r(x))).wrapInTerm(), /*unused*/b(), { ~q(y,x) } },
    //   { (~q(y,b)).wrapInTerm(), /*unused*/b(), { } },
    //   { q(z,r(b)).wrapInTerm(), /*unused*/b(), { q(z,b) } } }
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

  // checkTemplateBranches(handler, p, {
  //   { p(r(r(x))), { p(x) } },
  //   { p(r(r(x))), { p(r(x)) } },
  //   { p(b),       { } },
  //   { p(r(b)),    { } }
  // });

  // checkTemplateBranches(handler, q, {
  //   { q(y,r(x)), { q(y,x) } },
  //   { q(y,b),    { } }
  // });
}

// non-term-algebra sorts are ignored
TEST_FUN(test_05) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR)
  DECL_SORT(t)                     \
  DECL_FUNC(f1, {t}, t)            \
  DECL_PRED(p1, {t})               \
  DECL_DEF(defT, t)                \

  FunctionDefinitionHandler handler;
  addFunctionDefs(handler, {
    clause({ defT(f1(f1(x)), f1(x)) }),
    // clause({ p1(f1(x)).wrapInTerm(), /*unused*/b(), { p1(x) } } }
  });

  ASS(!handler.getInductionTemplate(f1(x).sugaredExpr().term()));
  // ASS(!handler.getInductionTemplate(p1.functor(), false));
}

// headers with non-term-algebra arguments are not discarded
// but trivial headers are added to ensure well-definedness
TEST_FUN(test_06) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR)
  FunctionDefinitionHandler handler;
  addFunctionDefs(handler, {
    // { { p(g(x)).wrapInTerm(), /*unused*/b(), { p(x) } } },
    clause({ def_s(f(r(x),g(y)), f(x,g(y))), }),
  });

  // checkTemplateBranches(handler, p, {
  //   { p(g(x)), { p(x) } },
  //   { p(x),    { } },
  // });

  checkTemplateBranches(handler, f(x,y), {
    { f(r(x),g(y)), { f(x,g(y)) } },
    { f(x,y),       { } },
  });
}

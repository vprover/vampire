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

#include "Kernel/FormulaUnit.hpp"

#include "Shell/FunctionDefinitionHandler.hpp"

using namespace Shell;

#define MY_SYNTAX_SUGAR                                                                    \
  DECL_DEFAULT_VARS                                                                        \
  DECL_VAR(x2, 2)                                                                          \
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
  DECL_SORT(u)                                                                             \
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

using FunctionDefs = std::initializer_list<std::initializer_list<std::tuple<
    TermSugar,TermSugar,std::initializer_list<Lit>>>>;

inline void addFunctionDefs(FunctionDefinitionHandler& handler, FunctionDefs functionDefs) {
  auto fu = new FormulaUnit(nullptr, FromInput(UnitInputType::AXIOM));
  for (const auto& fd : functionDefs) {
    Stack<FunctionDefinitionHandler::Branch> st;
    for (const auto& t : fd) {
      LiteralStack lits;
      for (const auto& l : get<2>(t)) {
        lits.push(l);
      }
      st.push({ get<0>(t).sugaredExpr().term(), get<1>(t).sugaredExpr(), lits });
    }
    handler.addFunction(st, fu);
  }
}

inline void checkTemplateBranches(FunctionDefinitionHandler& handler, const PredSugar& p, const vvector<pair<Term*, vvector<Term*>>>& v) {
  auto templ = handler.getInductionTemplate(p.functor(), false);
  ASS(templ);
  auto b = templ->branches();
  ASS_EQ(b.size(), v.size());
  TermList t;
  for (unsigned i = 0; i < b.size(); i++) {
    ASS_REP(b[i]._header == v[i].first, b[i]._header->toString() + " " + v[i].first->toString());
    auto r = b[i]._recursiveCalls;
    ASS_EQ(r.size(), v[i].second.size());
    for (unsigned j = 0; j < r.size(); j++) {
      ASS_REP(r[j] == v[i].second[j], r[j]->toString() + " " + v[i].second[j]->toString());
    }
  }
}

inline void checkTemplateBranches(FunctionDefinitionHandler& handler, const FuncSugar& f, const vvector<pair<TermSugar, vvector<TermSugar>>>& p) {
  auto templ = handler.getInductionTemplate(f.functor(), true);
  ASS(templ);
  auto b = templ->branches();
  ASS_EQ(b.size(), p.size());
  TermList t;
  for (unsigned i = 0; i < b.size(); i++) {
    ASS_EQ(b[i]._header, p[i].first.sugaredExpr().term());
    auto r = b[i]._recursiveCalls;
    ASS_EQ(r.size(), p[i].second.size());
    for (unsigned j = 0; j < r.size(); j++) {
      ASS_EQ(r[j], p[i].second[j].sugaredExpr().term());
    }
  }
}

// not well-founded functions
TEST_FUN(test_01) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR)
  FunctionDefinitionHandler handler;
  addFunctionDefs(handler, {
    { { f(r(x), r(y)), f(f(x, r(r(y))), y), { } } },
    { { g(r(x)), g(f(x,x)), { } } },
    { { h(x, y, r1(x, z)), h(y, y, z), { } },
      { h(r(x), y, z), h(x, x, r2(y,z)), { } } },
    { { p(r(r(x))).wrapInTerm(), /*unused*/b(), { p(y) } } },
    { { q(r1(x,y),r(z)).wrapInTerm(), /*unused*/b(), { q(y,r(z)), g(b) == b, q(z,b) } } },
  });

  ASS(!handler.getInductionTemplate(f.functor(), true));
  ASS(!handler.getInductionTemplate(g.functor(), true));
  ASS(!handler.getInductionTemplate(h.functor(), true));
  ASS(!handler.getInductionTemplate(p.functor(), false));
  ASS(!handler.getInductionTemplate(q.functor(), false));
}

// not useful functions (either no recursive calls or no argument changes in any recursive call)
TEST_FUN(test_02) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR)
  FunctionDefinitionHandler handler;
  addFunctionDefs(handler, {
    { { f(x, r(y)), g(f(x, r(y))), { } },
      { f(x, b), b, { } } },
    { { g(x), b, { } } }
  });

  ASS(!handler.getInductionTemplate(f.functor(), true));
  ASS(!handler.getInductionTemplate(g.functor(), true));
}

// adds missing cases
TEST_FUN(test_03) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR)
  FunctionDefinitionHandler handler;
  addFunctionDefs(handler, {
    { { f(r(x), r(y)), f(x,y), { } },
      { f(x,b), b, { } } },

    { { g(r(r(x))), g(x), { } } },

    { { h(b, x, y), b1, { } },
      { h(r(x), b, y), b2, { } },
      { h(r(x), b, r1(y,z)), h(x, b, z), { } } },

    { { p(r(r(x))).wrapInTerm(), /*unused*/b(), { ~p(x) } },
      { p(b).wrapInTerm(), /*unused*/b(), { f(b,b) == b } } },

    { { q(y,r(r(x))).wrapInTerm(), /*unused*/b(), { ~q(y,x) } },
      { (~q(r2(r1(x,y),z),b)).wrapInTerm(), /*unused*/b(), { } } }
  });

  checkTemplateBranches(handler, f, {
    { f(r(x),r(y)), { f(x,y) } },
    { f(x,b),       { } },
    { f(b,r(x4)),   { } } // added
  });

  checkTemplateBranches(handler, g, {
    { g(r(r(x))),   { g(x) } },
    { g(b),         { } }, // added
    { g(r(b)),      { } }, // added
  });

  checkTemplateBranches(handler, h, {
    { h(b, x, y),    { } },
    { h(r(x), b, y), { } },
    { h(r(x), b, r1(y,z)), { h(x, b, z) } },
    { h(r(x3), r(x4), x2), { } } // added
  });

  checkTemplateBranches(handler, p, {
    { p(r(r(x))), { p(x) } },
    { p(b),       { } },
    { p(r(b)),    { } } // added
  });

  checkTemplateBranches(handler, q, {
    { q(y,r(r(x))),            { q(y,x) } },
    { q(r2(r1(x,y),z),b),      { } },
    { q(b1,b),                 { } }, // added
    { q(b2,b),                 { } }, // added
    { q(r1(x4,x5),b),          { } }, // added
    { q(r2(b1,x7),b),          { } }, // added
    { q(r2(b2,x7),b),          { } }, // added
    { q(r2(r2(x10,x11),x7),b), { } }, // added
    { q(x,r(b)),               { } }  // added
  });
}

// correctly merges branches
TEST_FUN(test_04) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR)
  FunctionDefinitionHandler handler;
  addFunctionDefs(handler, {
    { { f(r(x), r(y)), f(x,y), { } },
      { f(r(x),r(x)), f(x,x), { } },
      { f(b,x), b, { } },
      { f(r(x),b), g(x), { } } },

    { { g(r(r(x))), g(r(x)), { } },
      { g(r(r(x))), g(x), { } },
      { g(r(b)), b, { } },
      { g(b), b, { } } },

    { { h(b, x, y), b1, { } },
      { h(r(x), y, z), h(x, y, z), { } },
      { h(r(x), z, y), h(x, z, y), { } } },

    { { p(r(r(x))).wrapInTerm(), /*unused*/b(), { ~p(x) } },
      { p(r(r(x))).wrapInTerm(), /*unused*/b(), { ~p(r(x)) } },
      { p(b).wrapInTerm(), /*unused*/b(), { } } },

    { { (~q(y,r(x))).wrapInTerm(), /*unused*/b(), { ~q(y,x) } },
      { (~q(y,b)).wrapInTerm(), /*unused*/b(), { } },
      { q(z,r(b)).wrapInTerm(), /*unused*/b(), { q(z,b) } } }
  });

  checkTemplateBranches(handler, f, {
    { f(r(x),r(y)), { f(x,y) } },
    { f(b,x),       { } },
    { f(r(x),b),    { } },
  });

  checkTemplateBranches(handler, g, {
    { g(r(r(x))),   { g(r(x)) } },
    { g(r(r(x))),   { g(x) } },
    { g(r(b)),      { } },
    { g(b),         { } },
  });

  checkTemplateBranches(handler, h, {
    { h(b, x, y),    { } },
    { h(r(x), y, z), { h(x, y, z) } }
  });

  checkTemplateBranches(handler, p, {
    { p(r(r(x))), { p(x) } },
    { p(r(r(x))), { p(r(x)) } },
    { p(b),       { } },
    { p(r(b)),    { } }
  });

  checkTemplateBranches(handler, q, {
    { q(y,r(x)), { q(y,x) } },
    { q(y,b),    { } }
  });
}

// non-term-algebra sorts are ignored
TEST_FUN(test_05) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR)
  DECL_SORT(t)                     \
  DECL_FUNC(f1, {t}, t)            \
  DECL_PRED(p1, {t})
  FunctionDefinitionHandler handler;
  addFunctionDefs(handler, {
    { { f1(f1(x)), f1(x), { } } },
    { { p1(f1(x)).wrapInTerm(), /*unused*/b(), { p1(x) } } }
  });

  ASS(!handler.getInductionTemplate(f1.functor(), true));
  ASS(!handler.getInductionTemplate(p1.functor(), false));
}

// headers with non-term-algebra arguments are not discarded
// but trivial headers are added to ensure well-definedness
TEST_FUN(test_06) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR)
  FunctionDefinitionHandler handler;
  addFunctionDefs(handler, {
    { { p(g(x)).wrapInTerm(), /*unused*/b(), { p(x) } } },
    { { f(r(x),g(y)), f(x,g(y)), { } } }
  });

  checkTemplateBranches(handler, p, {
    { p(g(x)), { p(x) } },
    { p(x),    { } },
  });

  checkTemplateBranches(handler, f, {
    { f(r(x),g(y)), { f(x,g(y)) } },
    { f(x,y),       { } },
  });
}

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

#include "Shell/InductionPreprocessor.hpp"

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

inline void checkTemplateBranches(const PredSugar& p, const vvector<pair<Term*, vvector<Term*>>>& v) {
  ASS(env.signature->getFnDefHandler()->hasInductionTemplate(p.functor(), false));
  auto templ = env.signature->getFnDefHandler()->getInductionTemplate(p.functor(), false);
  auto b = templ.branches();
  ASS_EQ(b.size(), v.size());
  TermList t;
  for (unsigned i = 0; i < b.size(); i++) {
    ASS_EQ(b[i]._header, v[i].first);
    auto r = b[i]._recursiveCalls;
    ASS_EQ(r.size(), v[i].second.size());
    for (unsigned j = 0; j < r.size(); j++) {
      ASS_EQ(r[j], v[i].second[j]);
    }
  }
}

inline void checkTemplateBranches(const FuncSugar& f, const vvector<pair<TermSugar, vvector<TermSugar>>>& p) {
  ASS(env.signature->getFnDefHandler()->hasInductionTemplate(f.functor(), true));
  auto templ = env.signature->getFnDefHandler()->getInductionTemplate(f.functor(), true);
  auto b = templ.branches();
  ASS_EQ(b.size(), p.size());
  TermList t;
  for (unsigned i = 0; i < b.size(); i++) {
    ASS_EQ(b[i]._header, p[i].first.toTerm().term());
    auto r = b[i]._recursiveCalls;
    ASS_EQ(r.size(), p[i].second.size());
    for (unsigned j = 0; j < r.size(); j++) {
      ASS_EQ(r[j], p[i].second[j].toTerm().term());
    }
  }
}


inline void checkInductionTerms(const InductionScheme& sch, const InductionTerms p) {
  ASS(sch.inductionTerms() == p);
}

inline void checkCases(const InductionScheme& sch, const vvector<pair<vmap<unsigned, TermList>, vvector<vmap<unsigned, TermList>>>>& p) {
  auto c = sch.cases();
  ASS_EQ(c.size(), p.size());
  TermList t;
  for (unsigned i = 0; i < c.size(); i++) {
    for (const auto& kv : p[i].first) {
      ASS(c[i]._step.findBinding(kv.first, t));
      ASS_EQ(t, kv.second);
    }
    auto r = c[i]._recursiveCalls;
    ASS_EQ(r.size(), p[i].second.size());
    for (unsigned j = 0; j < r.size(); j++) {
      for (const auto& kv : p[i].second[j]) {
        ASS(r[j].findBinding(kv.first, t));
        ASS_EQ(t, kv.second);
      }
    }
  }
}

// not well-founded functions
TEST_FUN(test_01) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR)
  DECL_FUNC_DEFS({ { clause({ f(r(x), r(y)) == f(f(x, r(r(y))), y) }),          0, false },   \
                   { clause({ g(r(x)) == g(f(x,x)) }),                          0, false },   \
                   { clause({ h(x, y, r1(x, z)) == h(y, y, z) }),               0, false },   \
                   { clause({ h(r(x), y, z) == h(x, x, r2(y,z)) }),             0, false },   \
                   { clause({ ~p(r(r(x))), ~p(y) }),                            0, false },   \
                   { clause({ q(r1(x,y),r(z)), ~q(y,r(z)), g(b) == b, q(z,b) }),0, false } })

  ASS(!env.signature->getFnDefHandler()->hasInductionTemplate(f.functor(), true));
  ASS(!env.signature->getFnDefHandler()->hasInductionTemplate(g.functor(), true));
  ASS(!env.signature->getFnDefHandler()->hasInductionTemplate(h.functor(), true));
  ASS(!env.signature->getFnDefHandler()->hasInductionTemplate(p.functor(), false));
  ASS(!env.signature->getFnDefHandler()->hasInductionTemplate(q.functor(), false));
}

// not useful functions (either no recursive calls or no argument changes in any recursive call)
TEST_FUN(test_02) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR)
  DECL_FUNC_DEFS({ { clause({ g(f(x, r(y))) == f(x, r(y)) }),                0, true  },   \
                   { clause({ f(x, b) == b }),                               0, false },   \
                   { clause({ g(x) == b }),                                  0, false } })

  ASS(!env.signature->getFnDefHandler()->hasInductionTemplate(f.functor(), true));
  ASS(!env.signature->getFnDefHandler()->hasInductionTemplate(g.functor(), true));
}

// adds missing cases
TEST_FUN(test_03) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR)

  DECL_FUNC_DEFS({ { clause({ f(x,y) == f(r(x), r(y)) }),                    0, true  },   \
                   { clause({ f(x,b) == b }),                                0, false },   \
                                                                                           \
                   { clause({ g(r(r(x))) == g(x) }),                         0, false },   \
                                                                                           \
                   { clause({ h(b, x, y) == b1 }),                           0, false },   \
                   { clause({ h(r(x), b, y) == b2 }),                        0, false },   \
                   { clause({ h(r(x), b, r1(y,z)) == h(x, b, z) }),          0, false },   \
                                                                                           \
                   { clause({ p(r(r(x))), ~p(x) }),                          0, false },   \
                   { clause({ p(b), f(b,b) == b }),                          0, false },   \
                                                                                           \
                   { clause({ q(y,r(r(x))), ~q(y,x) }),                      0, false },   \
                   { clause({ ~q(r2(r1(x,y),z),b) }),                        0, false } })

  checkTemplateBranches(f, {
    { f(r(x),r(y)), { f(x,y) } },
    { f(x,b),       { } },
    { f(b,r(x4)),   { } } // added
  });

  checkTemplateBranches(g, {
    { g(r(r(x))),   { g(x) } },
    { g(b),         { } }, // added
    { g(r(b)),      { } }, // added
  });

  checkTemplateBranches(h, {
    { h(b, x, y),    { } },
    { h(r(x), b, y), { } },
    { h(r(x), b, r1(y,z)), { h(x, b, z) } },
    { h(r(x3), r(x4), x2), { } } // added
  });

  checkTemplateBranches(p, {
    { p(r(r(x))), { p(x) } },
    { p(b),       { } },
    { p(r(b)),    { } } // added
  });

  checkTemplateBranches(q, {
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

  DECL_FUNC_DEFS({ { clause({ f(x,y) == f(r(x), r(y)) }),                    0, true  },   \
                   { clause({ f(r(x),r(x)) == f(x,x) }),                     0, false },   \
                   { clause({ b == f(b,x) }),                                0, true  },   \
                   { clause({ f(r(x),b) == g(x) }),                          0, false },   \
                                                                                           \
                   { clause({ g(r(r(x))) == g(r(x)) }),                      0, false },   \
                   { clause({ g(r(r(x))) == g(x) }),                         0, false },   \
                   { clause({ g(r(b)) == b }),                               0, false },   \
                   { clause({ g(b) == b }),                                  0, false },   \
                                                                                           \
                   { clause({ h(b, x, y) == b1 }),                           0, false },   \
                   { clause({ h(r(x), y, z) == h(x, y, z) }),                0, false },   \
                   { clause({ h(r(x), z, y) == h(x, z, y) }),                0, false },   \
                                                                                           \
                   { clause({ p(r(r(x))), ~p(x) }),                          0, false },   \
                   { clause({ p(r(r(x))), ~p(r(x)) }),                       0, false },   \
                   { clause({ p(b) }),                                       0, false },   \
                                                                                           \
                   { clause({ ~q(y,r(x)), ~q(y,x) }),                        0, false },   \
                   { clause({ ~q(y,b) }),                                    0, false },   \
                   { clause({ q(z,r(b)), q(z,b) }),                          0, false } })

  checkTemplateBranches(f, {
    { f(r(x),r(y)), { f(x,y) } },
    { f(b,x),       { } },
    { f(r(x),b),    { } },
  });

  checkTemplateBranches(g, {
    { g(r(r(x))),   { g(r(x)) } },
    { g(r(r(x))),   { g(x) } },
    { g(r(b)),      { } },
    { g(b),         { } },
  });

  checkTemplateBranches(h, {
    { h(b, x, y),    { } },
    { h(r(x), y, z), { h(x, y, z) } }
  });

  checkTemplateBranches(p, {
    { p(r(r(x))), { p(x) } },
    { p(r(r(x))), { p(r(x)) } },
    { p(b),       { } },
    { p(r(b)),    { } }
  });

  checkTemplateBranches(q, {
    { q(y,r(x)), { q(y,x) } },
    { q(y,b),    { } }
  });
}

// non-term-algebra sorts are ignored
TEST_FUN(test_05) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR)
  DECL_SORT(t)                                                                             \
  DECL_FUNC(f1, {t}, t)                                                                    \
  DECL_PRED(p1, {t})                                                                       \
  DECL_FUNC_DEFS({ { clause({ f1(f1(x)) == f1(x) }),                         0, false  },  \
                   { clause({ p1(f1(x)), p1(x) }),                           0, false  } })

  ASS(!env.signature->getFnDefHandler()->hasInductionTemplate(f1.functor(), true));
  ASS(!env.signature->getFnDefHandler()->hasInductionTemplate(p1.functor(), false));
}

// headers with non-term-algebra arguments are not discarded
// but trivial headers are added to ensure well-definedness
TEST_FUN(test_06) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR)
  DECL_FUNC_DEFS({ { clause({ p(g(x)), p(x) }),                              0, false  },  \
                   { clause({ f(r(x),g(y)) == f(x,g(y)) }),                  0, false } })

  checkTemplateBranches(p, {
    { p(g(x)), { p(x) } },
    { p(x),    { } },
  });

  checkTemplateBranches(f, {
    { f(r(x),g(y)), { f(x,g(y)) } },
    { f(x,y),       { } },
  });
}

// structural induction schemes
TEST_FUN(test_07) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR)

  auto t1 = f(x,y);
  vvector<InductionScheme> schemes;
  env.signature->getFnDefHandler()->requestStructuralInductionScheme(t1.toTerm().term(), schemes);
  ASS_EQ(schemes.size(), 1);
  checkInductionTerms(schemes[0], { { t1.toTerm().term(), 0 } });
  checkCases(schemes[0], {
    { { { 0, b.toTerm() } },    { } },
    { { { 0, r(y).toTerm() } }, { { { 0, y.toTerm() } } } }
  });

  auto t2 = h(g(g(b)),b,b1);
  env.signature->getFnDefHandler()->requestStructuralInductionScheme(t2.toTerm().term(), schemes);
  ASS_EQ(schemes.size(), 2);

  checkInductionTerms(schemes[1], { { t2.toTerm().term(), 0 } });
  checkCases(schemes[1], {
    { { { 0, b1.toTerm() } },        { } },
    { { { 0, b2.toTerm() } },        { } },
    { { { 0, r1(y,z).toTerm() } },   { { { 0, z.toTerm() } } } },
    { { { 0, r2(x3,x4).toTerm() } }, { { { 0, x3.toTerm() } } } }
  });
}

// induction schemes from recursive functions
TEST_FUN(test_08) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR)
  DECL_SKOLEM_CONST(sk1, s)                                                                   \
  DECL_SKOLEM_CONST(sk2, s)                                                                   \
  DECL_SKOLEM_CONST(sk3, u)                                                                   \
  DECL_FUNC_DEFS({ { clause({ f(r(x), r(r(y))) == f(f(x, r(r(y))), y) }),       0, false },   \
                   { clause({ q(r1(x,y),r(z)), ~q(y,r(z)), q(y,z) }),           0, false } })

  // TODO(mhajdu): with options set, complex terms should be tested as well
  vset<InductionScheme> schemes;
  auto ft = env.signature->getFnDefHandler()->getInductionTemplate(f.functor(), true);
  ft.requestInductionScheme(f(sk1,sk2).toTerm().term(), schemes);
  ASS_EQ(schemes.size(), 1);
  checkInductionTerms(*schemes.begin(), { { sk1.toTerm().term(), 0 }, { sk2.toTerm().term(), 1 } });
  checkCases(*schemes.begin(), {
    { { { 0, r(x2).toTerm() }, { 1, r(r(x3)).toTerm() } }, { { { 0, f(x2,r(r(x3))).toTerm() }, { 1, x3.toTerm() } },
                                                             { { 0, x2.toTerm() }, { 1, r(r(x3)).toTerm() } } } },
    { { { 0, b.toTerm() }, { 1, x4.toTerm() } },           { } },
    { { { 0, x5.toTerm() }, { 1, b.toTerm() } },           { } },
    { { { 0, x6.toTerm() }, { 1, r(b).toTerm() } },        { } },
  });

  schemes.clear();
  ft.requestInductionScheme(f(sk1,sk1).toTerm().term(), schemes);
  ASS_EQ(schemes.size(), 1);
  checkInductionTerms(*schemes.begin(), { { sk1.toTerm().term(), 0 } });
  checkCases(*schemes.begin(), {
    { { { 0, r(r(y)).toTerm() } }, { } },
    { { { 0, b.toTerm() } },       { } },
    { { { 0, b.toTerm() } },       { } },
    { { { 0, r(b).toTerm() } },    { } },
  });

  schemes.clear();
  auto qt = env.signature->getFnDefHandler()->getInductionTemplate(q.functor(), false);
  qt.requestInductionScheme(q(sk3,sk1), schemes);
  ASS_EQ(schemes.size(), 1);
  checkInductionTerms(*schemes.begin(), { { sk3().toTerm().term(), 0 }, { sk1().toTerm().term(), 1 } });
  checkCases(*schemes.begin(), {
    { { { 0, r1(x2,x3).toTerm() }, { 1, r(x4).toTerm() } }, { { { 0, x3.toTerm() }, { 1, r(x4).toTerm() } },
                                                              { { 0, x3.toTerm() }, { 1, x4.toTerm() } } } },
    { { { 0, b1.toTerm() }, { 1, x5.toTerm() } },           { } },
    { { { 0, b2.toTerm() }, { 1, x6.toTerm() } },           { } },
    { { { 0, r2(x7,x8).toTerm() }, { 1, x9.toTerm() } },    { } },
    { { { 0, x10.toTerm() }, { 1, b.toTerm() } },           { } },
  });

  // no scheme is generated if no Skolems are present
  // in one of the inductive arguments or the term is non-ground
  schemes.clear();
  ft.requestInductionScheme(f(sk1,x).toTerm().term(), schemes);
  ft.requestInductionScheme(f(b,sk1).toTerm().term(), schemes);
  qt.requestInductionScheme(q(sk3,x), schemes);
  qt.requestInductionScheme(q(b1,sk1), schemes);
  qt.requestInductionScheme(q(r1(b,b1),sk1), schemes);
  ASS(schemes.empty());
}

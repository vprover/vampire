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

inline void checkInductionTerms(const InductionScheme& sch, const vmap<Term*, unsigned> p) {
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

// not useful functions
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
                   { clause({ ~q(r2(r1(x,y),z),b) }),                         0, false } })

  auto fb = env.signature->getFnDefHandler()->getInductionTemplate(f.functor(), true).branches();
  ASS_EQ(fb.size(), 3);
  ASS_EQ(fb[0]._header, f(r(x),r(y)).toTerm().term());
  ASS_EQ(fb[1]._header, f(x,b).toTerm().term());
  ASS_EQ(fb[2]._header, f(b,r(x4)).toTerm().term()); // added

  auto gb = env.signature->getFnDefHandler()->getInductionTemplate(g.functor(), true).branches();
  ASS_EQ(gb.size(), 3);
  ASS_EQ(gb[0]._header, g(r(r(x))).toTerm().term());
  ASS_EQ(gb[1]._header, g(b).toTerm().term()); // added
  ASS_EQ(gb[2]._header, g(r(b)).toTerm().term()); // added

  auto hb = env.signature->getFnDefHandler()->getInductionTemplate(h.functor(), true).branches();
  ASS_EQ(hb.size(), 4);
  ASS_EQ(hb[0]._header, h(b, x, y).toTerm().term());
  ASS_EQ(hb[1]._header, h(r(x), b, y).toTerm().term());
  ASS_EQ(hb[2]._header, h(r(x), b, r1(y,z)).toTerm().term());
  ASS_EQ(hb[3]._header, h(r(x3), r(x4), x2).toTerm().term()); // added

  auto pb = env.signature->getFnDefHandler()->getInductionTemplate(p.functor(), false).branches();
  ASS_EQ(pb.size(), 3);
  ASS_EQ(pb[0]._header, p(r(r(x))));
  ASS_EQ(pb[1]._header, p(b));
  ASS_EQ(pb[2]._header, p(r(b))); // added

  auto qb = env.signature->getFnDefHandler()->getInductionTemplate(q.functor(), false).branches();
  ASS_EQ(qb.size(), 9);
  ASS_EQ(qb[0]._header, q(y,r(r(x))));
  ASS_EQ(qb[1]._header, q(r2(r1(x,y),z),b));
  ASS_EQ(qb[2]._header, q(b1,b)); // added
  ASS_EQ(qb[3]._header, q(b2,b)); // added
  ASS_EQ(qb[4]._header, q(r1(x4,x5),b)); // added
  ASS_EQ(qb[5]._header, q(r2(b1,x7),b)); // added
  ASS_EQ(qb[6]._header, q(r2(b2,x7),b)); // added
  ASS_EQ(qb[7]._header, q(r2(r2(x10,x11),x7),b)); // added
  ASS_EQ(qb[8]._header, q(x,r(b))); // added
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

  auto fb = env.signature->getFnDefHandler()->getInductionTemplate(f.functor(), true).branches();
  ASS_EQ(fb.size(), 3);
  ASS_EQ(fb[0]._header, f(r(x),r(y)).toTerm().term());
  ASS_EQ(fb[0]._recursiveCalls.size(), 1);
  ASS_EQ(fb[0]._recursiveCalls[0], f(x,y).toTerm().term());
  ASS_EQ(fb[1]._header, f(b,x).toTerm().term());
  ASS(fb[1]._recursiveCalls.empty());
  ASS_EQ(fb[2]._header, f(r(x),b).toTerm().term());
  ASS(fb[2]._recursiveCalls.empty());

  auto gb = env.signature->getFnDefHandler()->getInductionTemplate(g.functor(), true).branches();
  ASS_EQ(gb.size(), 4);
  ASS_EQ(gb[0]._header, g(r(r(x))).toTerm().term());
  ASS_EQ(gb[0]._recursiveCalls.size(), 1);
  ASS_EQ(gb[0]._recursiveCalls[0], g(r(x)).toTerm().term());
  ASS_EQ(gb[1]._header, g(r(r(x))).toTerm().term());
  ASS_EQ(gb[1]._recursiveCalls.size(), 1);
  ASS_EQ(gb[1]._recursiveCalls[0], g(x).toTerm().term());
  ASS_EQ(gb[2]._header, g(r(b)).toTerm().term());
  ASS(gb[2]._recursiveCalls.empty());
  ASS_EQ(gb[3]._header, g(b).toTerm().term());
  ASS(gb[3]._recursiveCalls.empty());

  auto hb = env.signature->getFnDefHandler()->getInductionTemplate(h.functor(), true).branches();
  ASS_EQ(hb.size(), 2);
  ASS_EQ(hb[0]._header, h(b, x, y).toTerm().term());
  ASS(hb[0]._recursiveCalls.empty());
  ASS_EQ(hb[1]._header, h(r(x), y, z).toTerm().term());
  ASS_EQ(hb[1]._recursiveCalls.size(), 1);
  ASS_EQ(hb[1]._recursiveCalls[0], h(x, y, z).toTerm().term());

  auto pb = env.signature->getFnDefHandler()->getInductionTemplate(p.functor(), false).branches();
  ASS_EQ(pb.size(), 4);
  ASS_EQ(pb[0]._header, p(r(r(x))));
  ASS_EQ(pb[0]._recursiveCalls.size(), 1);
  ASS_EQ(pb[0]._recursiveCalls[0], p(x));
  ASS_EQ(pb[1]._header, p(r(r(x))));
  ASS_EQ(pb[1]._recursiveCalls.size(), 1);
  ASS_EQ(pb[1]._recursiveCalls[0], p(r(x)));
  ASS_EQ(pb[2]._header, p(b));
  ASS(pb[2]._recursiveCalls.empty());
  ASS_EQ(pb[3]._header, p(r(b))); // added
  ASS(pb[3]._recursiveCalls.empty());

  auto qb = env.signature->getFnDefHandler()->getInductionTemplate(q.functor(), false).branches();
  ASS_EQ(qb.size(), 2);
  ASS_EQ(qb[0]._header, q(y,r(x)));
  ASS_EQ(qb[0]._recursiveCalls.size(), 1);
  ASS_EQ(qb[0]._recursiveCalls[0], q(y,x));
  ASS_EQ(qb[1]._header, q(y,b));
  ASS(qb[1]._recursiveCalls.empty());
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

// non-term-algebra header arguments are OK but trivial headers are added for well-definedness are ignored
TEST_FUN(test_06) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR)
  DECL_FUNC_DEFS({ { clause({ p(g(x)), p(x) }),                              0, false  },  \
                   { clause({ f(r(x),g(y)) == f(x,g(y)) }),                  0, false } })

  auto pb = env.signature->getFnDefHandler()->getInductionTemplate(p.functor(), false).branches();
  ASS_EQ(pb.size(), 2);
  ASS(pb[1]._recursiveCalls.empty());
  ASS_EQ(pb[1]._header, p(x));
  auto fb = env.signature->getFnDefHandler()->getInductionTemplate(f.functor(), true).branches();
  ASS_EQ(fb.size(), 2);
  ASS(fb[1]._recursiveCalls.empty());
  ASS_EQ(fb[1]._header, f(x,y).toTerm().term());
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

  TermList t;
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
  DECL_INDUCTION_SKOLEM_CONST(sk1, s)                                                         \
  DECL_INDUCTION_SKOLEM_CONST(sk2, s)                                                         \
  DECL_INDUCTION_SKOLEM_CONST(sk3, u)                                                         \
  DECL_FUNC_DEFS({ { clause({ f(r(x), r(r(y))) == f(f(x, r(r(y))), y) }),       0, false },   \
                   { clause({ q(r1(x,y),r(z)), ~q(y,r(z)), q(y,z) }),           0, false } })

  vset<InductionScheme> schemes;
  auto ft = env.signature->getFnDefHandler()->getInductionTemplate(f.functor(), true);
  ft.requestInductionScheme(f(sk1,sk2).toTerm().term(), schemes);
  ASS_EQ(schemes.size(), 1);

  checkInductionTerms(*schemes.begin(), { { sk1().toTerm().term(), 0 }, { sk2().toTerm().term(), 1 } });
  checkCases(*schemes.begin(), {
    { { { 0, r(x2).toTerm() }, { 1, r(r(x3)).toTerm() } }, { { { 0, f(x2,r(r(x3))).toTerm() }, { 1, x3.toTerm() } },
                                                             { { 0, x2.toTerm() }, { 1, r(r(x3)).toTerm() } } } },
    { { { 0, b.toTerm() }, { 1, x4.toTerm() } },           { } },
    { { { 0, x5.toTerm() }, { 1, b.toTerm() } },           { } },
    { { { 0, x6.toTerm() }, { 1, r(b).toTerm() } },        { } },
  });

  schemes.clear();
  auto t2 = f(sk1,sk1);
  ft.requestInductionScheme(t2.toTerm().term(), schemes);
  ASS_EQ(schemes.size(), 1);
  checkInductionTerms(*schemes.begin(), { { sk1().toTerm().term(), 0 } });
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
}
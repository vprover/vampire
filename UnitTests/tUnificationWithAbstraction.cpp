/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#include "Debug/Assertion.hpp"
#include "Forwards.hpp"
#include "Indexing/SubstitutionTree.hpp"

#include "Shell/Options.hpp"
#include "Test/TestUtils.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/UnificationWithAbstraction.hpp"
#include "Test/AlascaTestUtils.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/LiteralSubstitutionTree.hpp"
#include "Indexing/TermSubstitutionTree.hpp"

#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"

using namespace std;
using namespace Kernel;
using namespace Indexing;

Clause* unit(Literal* lit)
{ return clause({ lit }); }

static const auto tld = [](auto t) { return TermWithoutValue(TypedTermList(t)); };


unique_ptr<TermSubstitutionTree<TermWithoutValue>> getTermIndexHOL()
{ return std::make_unique<TermSubstitutionTree<TermWithoutValue>>(); }

unique_ptr<TermSubstitutionTree<TermWithoutValue>> getTermIndex()
{ return std::make_unique<TermSubstitutionTree<TermWithoutValue>>();
}

template<class... Args>
Stack<Literal*> constraints(Args... args) {
  Stack<Literal*> lits;
  lits.loadFromIterator(iterItems<Literal*>(args...));
  return lits;
}

inline auto noConstraints() { return constraints(); } 


auto getLiteralIndex()
{ return std::make_unique<LiteralSubstitutionTree<LiteralClause>>(); }

template<class TermOrLit>
struct UnificationResultSpec {
  TermOrLit querySigma;
  TermOrLit resultSigma;
  Stack<Literal*> constraints;
  bool alascaSimpl = false;

  friend bool operator==(UnificationResultSpec const& l, UnificationResultSpec const& r)
  {
    static shared_ptr<AlascaState> state = testAlascaState();
    auto eq = [&](auto t1, auto t2) { 
      return (l.alascaSimpl || r.alascaSimpl) ? state->norm().equivalent(t1, t2)
                                            : Test::TestUtils::eqModAC(t1, t2);
    };
    return eq(l.querySigma, r.querySigma)
       &&  eq(l.resultSigma, r.resultSigma)
       &&  Test::TestUtils::permEq(l.constraints, r.constraints,
             [&](auto& l, auto& r) { return eq(l,r); });
  }

  friend std::ostream& operator<<(std::ostream& out, UnificationResultSpec const& self)
  { 
    out << "{ querySigma = " << Test::pretty(self.querySigma) << ", resultSigma = " << Test::pretty(self.resultSigma) << ", cons = [ ";
    for (auto& c : self.constraints) {
      out << *c << ", ";
    }
    return out << "] }";
  }
};

using TermUnificationResultSpec    = UnificationResultSpec<TermList>;
using LiteralUnificationResultSpec = UnificationResultSpec<Literal*>;

void checkLiteralMatches(LiteralSubstitutionTree<LiteralClause>& index, Options::UnificationWithAbstraction uwa, bool fixedPointIteration, Literal* lit, Stack<LiteralUnificationResultSpec> expected)
{
  Stack<LiteralUnificationResultSpec> is;
  for (auto qr : iterTraits(index.getUwa(lit, /* complementary */ false, uwa, fixedPointIteration)) ) {

    is.push(LiteralUnificationResultSpec {
        .querySigma = qr.unifier->subs().apply(lit, /* result */ subsTreeQueryBank(0)),
        .resultSigma = qr.unifier->subs().apply(qr.data->literal, /* result */ subsTreeInternalBank(0)),
        .constraints = *qr.unifier->constr().literals(qr.unifier->subs()),
    });
  }
  if (Test::TestUtils::permEq(is, expected, [](auto& l, auto& r) { return l == r; })) {
    cout << "[  OK  ] " << *lit << endl;
  } else {
    cout << "[ FAIL ] " << *lit << endl;
    cout << "tree: " << Output::multiline(index, 1) << endl;
    cout << "query: " << *lit << endl;

    cout << "is:" << endl;
    for (auto& x : is)
      cout << "         " << x << endl;

    cout << "expected:" << endl;
    for (auto& x : expected)
      cout << "         " << x << endl;

    ASSERTION_VIOLATION
  }
}

template<class F>
void checkTermMatchesWithUnifFun(TermSubstitutionTree<TermWithoutValue>& index, TypedTermList term, Stack<TermUnificationResultSpec> expected, F unifFun)
{
  Stack<TermUnificationResultSpec> is;
  for (auto qr : iterTraits(unifFun(index, term))) {
    is.push(TermUnificationResultSpec {
        .querySigma  = qr.unifier->subs().apply(term, /* result */ subsTreeQueryBank(0)),
        .resultSigma = qr.unifier->subs().apply(qr.data->term, /* result */ subsTreeInternalBank(0)),
        .constraints = *qr.unifier->constr().literals(qr.unifier->subs()),
    });
  }
  if (Test::TestUtils::permEq(is, expected, [](auto& l, auto& r) { return l == r; })) {
    cout << "[  OK  ] " << term << endl;
  } else {
    cout << "[ FAIL ] " << term << endl;
    cout << "tree: " << Output::multiline(index, 1) << endl;
    cout << "query: " << term << endl;

    cout << "is:" << endl;
    for (auto& x : is)
      cout << "         " << x << endl;

    cout << "expected:" << endl;
    for (auto& x : expected)
      cout << "         " << x << endl;

    ASSERTION_VIOLATION
  }

}

void checkTermMatches(TermSubstitutionTree<TermWithoutValue>& index, Options::UnificationWithAbstraction uwa, bool fixedPointIteration, TypedTermList term, Stack<TermUnificationResultSpec> expected)
{
  return checkTermMatchesWithUnifFun(index, term, expected, 
      [&](auto& idx, auto t) { return idx.getUwa(term, uwa, fixedPointIteration); });
}


struct IndexTest {
  std::unique_ptr<TermSubstitutionTree<TermWithoutValue>> index;
  Options::UnificationWithAbstraction uwa;
  bool fixedPointIteration = false;
  Stack<TypedTermList> insert;
  TermSugar query;
  Stack<TermUnificationResultSpec> expected;

  void run() {
    for (auto x : this->insert) {
      index->insert(TermWithoutValue(x));
    }

    checkTermMatches(*this->index, uwa, fixedPointIteration, TypedTermList(this->query, this->query.sort()),this->expected);

  }
};


struct LiteralIndexTest {
  unique_ptr<LiteralSubstitutionTree<LiteralClause>> index;
  Options::UnificationWithAbstraction uwa;
  bool fixedPointIteration = false;
  Stack<Literal*> insert;
  Literal* query;
  Stack<LiteralUnificationResultSpec> expected;

  void run() {
    DECL_PRED(dummy, {})
    for (auto x : this->insert) {
      index->insert(LiteralClause{ x, unit(dummy()) });
    }

    checkLiteralMatches(*index, uwa, fixedPointIteration, query, expected);
  }
};

#define SUGAR(Num)                                                                        \
   __ALLOW_UNUSED(                                                                        \
      DECL_DEFAULT_VARS                                                                   \
      DECL_VAR(x0, 0)                                                                     \
      DECL_VAR(x1, 1)                                                                     \
      DECL_VAR(x2, 2)                                                                     \
      DECL_VAR(x3, 3)                                                                     \
                                                                                          \
      DECL_VAR(S0, 500)                                                                   \
      DECL_VAR(S1, 501)                                                                   \
      DECL_VAR(S2, 502)                                                                   \
      DECL_VAR(S3, 503)                                                                   \
      DECL_VAR(S4, 504)                                                                   \
      DECL_VAR(S5, 505)                                                                   \
      DECL_VAR(S6, 506)                                                                   \
      DECL_VAR(S7, 507)                                                                   \
      DECL_VAR(S8, 508)                                                                   \
      DECL_VAR(S9, 509)                                                                   \
      DECL_VAR(S10, 510)                                                                  \
      DECL_VAR(S11, 511)                                                                  \
      DECL_VAR(S12, 512)                                                                  \
                                                                                          \
      NUMBER_SUGAR(Num)                                                                   \
      mkAlascaSyntaxSugar(Num ## Traits{}); \
      DECL_SORT(s)                                                                        \
      DECL_FUNC(r2s, {Num}, s)                                                            \
      DECL_FUNC(s2r, {s}, Num)                                                            \
      DECL_PRED(p, {Num})                                                                 \
      DECL_FUNC(f, {Num}, Num)                                                            \
      DECL_FUNC(g, {Num}, Num)                                                            \
      DECL_FUNC(h, {Num}, Num)                                                            \
      DECL_FUNC(f2, {Num, Num}, Num)                                                      \
      DECL_FUNC(fa, {Num, Num}, Num)                                                      \
      DECL_FUNC(g2, {Num, Num}, Num)                                                      \
      DECL_CONST(a, Num)                                                                  \
      DECL_CONST(b, Num)                                                                  \
      DECL_CONST(c, Num)                                                                  \
    )                                                                                     \


#define INDEX_TEST(name, sugar, ...)                                                      \
  TEST_FUN(name) {                                                                        \
       __ALLOW_UNUSED(sugar)                                                              \
       __VA_ARGS__.run();                                                                 \
  }                                                                                       \

INDEX_TEST(term_indexing_one_side_interp_01,
    SUGAR(Rat),
    IndexTest {
      .index = getTermIndex(),
      .uwa = Options::UnificationWithAbstraction::ONE_INTERP,
      .fixedPointIteration = false,
      .insert = {
        f(1 + num(1)),
        f(1 + a),
      },
      .query = f(x),
      .expected = { 

          TermUnificationResultSpec 
          { .querySigma  = f(1 + a),
            .resultSigma = f(1 + a),
            .constraints = noConstraints() }, 

          TermUnificationResultSpec 
          { .querySigma  = f(1 + num(1)),
            .resultSigma = f(1 + num(1)),
            .constraints = noConstraints() }, 

      },
    })


INDEX_TEST(term_indexing_one_side_interp_02, 
    SUGAR(Rat),
    IndexTest {
      .index = getTermIndex(),
      .uwa = Options::UnificationWithAbstraction::ONE_INTERP,
      .fixedPointIteration = false,
      .insert = {
        f(1 + num(1)),
        f(1 + a),
      },
      .query = g(x),
      .expected = Stack<TermUnificationResultSpec>(),
    })
 
INDEX_TEST(term_indexing_one_side_interp_03, 
    SUGAR(Rat),
    IndexTest {
      .index = getTermIndex(),
      .uwa = Options::UnificationWithAbstraction::ONE_INTERP,
      .fixedPointIteration = false,
      .insert = {
        1 + num(1),
        1 + a,
      },
      .query = x.sort(Rat),
      .expected = { 

        TermUnificationResultSpec 
        { .querySigma  = 1 + a,
          .resultSigma = 1 + a,
          .constraints = noConstraints() }, 

        TermUnificationResultSpec 
        { .querySigma  = 1 + num(1),
          .resultSigma = 1 + num(1),
          .constraints = noConstraints() }, 

      }
    })


INDEX_TEST(term_indexing_one_side_interp_04, 
    SUGAR(Rat),
    IndexTest {
      .index = getTermIndex(),
      .uwa = Options::UnificationWithAbstraction::ONE_INTERP,
      .fixedPointIteration = false,
      .insert = {
        1 + num(1),
        1 + a,
      },
      .query = b + 2,
      .expected = { 

        TermUnificationResultSpec 
        { .querySigma  = 2 + b,
          .resultSigma = 1 + a,
          .constraints = { 1 + a != 2 + b, } },

        TermUnificationResultSpec 
        { .querySigma  = 2 + b,
          .resultSigma = 1 + num(1),
          .constraints = { 2 + b != 1 + num(1), } }, 

      }
    })



INDEX_TEST(term_indexing_one_side_interp_04_b, 
    SUGAR(Rat),
    IndexTest {
      .index = getTermIndex(),
      .uwa = Options::UnificationWithAbstraction::ONE_INTERP,
      .fixedPointIteration = false,
      .insert = {
        1 + a,
      },
      .query = 2 + a,
      .expected = { 

        TermUnificationResultSpec 
        { .querySigma  = 2 + a,
          .resultSigma = 1 + a,
          .constraints = { 1 + a != 2 + a, } },


      }
    })


INDEX_TEST(term_indexing_one_side_interp_04_c, 
    SUGAR(Rat),
    IndexTest {
      .index = getTermIndex(),
      .uwa = Options::UnificationWithAbstraction::ONE_INTERP,
      .fixedPointIteration = false,
      .insert = {
        f(1 + num(1)),
        f(1 + a),
      },
      .query = f( b + 2 ),
      .expected = { 

        TermUnificationResultSpec 
        { .querySigma  = f( 2 + b ),
          .resultSigma = f( 1 + a ),
          .constraints = { 1 + a != 2 + b, } },

        TermUnificationResultSpec 
        { .querySigma  = f( 2 + b ),
          .resultSigma = f( 1 + num(1) ),
          .constraints = { 2 + b != 1 + num(1), } }, 

      }
    })

INDEX_TEST(term_indexing_one_side_interp_04_d, 
    SUGAR(Rat),
    IndexTest {
      .index = getTermIndex(),
      .uwa = Options::UnificationWithAbstraction::ONE_INTERP,
      .fixedPointIteration = false,
      .insert = {
        g(f(1 + num(1))),
        g(f(1 + a)),
      },
      .query = g(f( b + 2 )),
      .expected = { 

        TermUnificationResultSpec 
        { .querySigma  = g(f( 2 + b )),
          .resultSigma = g(f( 1 + a )),
          .constraints = { 1 + a != 2 + b, } },

        TermUnificationResultSpec 
        { .querySigma  = g(f( 2 + b )),
          .resultSigma = g(f( 1 + num(1) )),
          .constraints = { 2 + b != 1 + num(1), } }, 

      }
    })

INDEX_TEST(term_indexing_one_side_interp_05, 
    SUGAR(Rat),
    IndexTest {
      .index = getTermIndex(),
      .uwa = Options::UnificationWithAbstraction::ONE_INTERP,
      .fixedPointIteration = false,
      .insert = {
        1 + num(1),
        1 + a,
        a,
      },
      .query = b + 2, 
      .expected = {
        TermUnificationResultSpec 
        { .querySigma  = 2 + b,
          .resultSigma = 1 + a,
          .constraints = { 1 + a != 2 + b, } },

        TermUnificationResultSpec 
        { .querySigma  = 2 + b,
          .resultSigma = 1 + num(1),
          .constraints = { 2 + b != 1 + num(1), } }, 

        TermUnificationResultSpec 
        { .querySigma  = 2 + b,
          .resultSigma = a,
          .constraints = { 2 + b != a, } }, 

      }
})


INDEX_TEST(term_indexing_one_side_interp_06, 
    SUGAR(Rat),
    IndexTest {
      .index = getTermIndex(),
      .uwa = Options::UnificationWithAbstraction::ONE_INTERP,
      .fixedPointIteration = false,
      .insert = {
        1 + num(1),
        1 + a,
        a,
      },
      .query = x.sort(Rat),
      .expected = {
        TermUnificationResultSpec 
        { .querySigma  = 1 + a,
          .resultSigma = 1 + a,
          .constraints = Stack<Literal*>{} },

        TermUnificationResultSpec 
        { .querySigma  = 1 + num(1),
          .resultSigma = 1 + num(1),
          .constraints = Stack<Literal*>{} }, 

        TermUnificationResultSpec 
        { .querySigma  = a,
          .resultSigma = a,
          .constraints = Stack<Literal*>{} }, 

      }
})


INDEX_TEST(term_indexing_one_side_interp_07, 
    SUGAR(Rat),
    IndexTest {
      .index = getTermIndex(),
      .uwa = Options::UnificationWithAbstraction::ONE_INTERP,
      .fixedPointIteration = false,
      .insert = {
        1 + num(1),
        1 + a,
        a,
        f(x),
      },
      .query = f(a),
      .expected =  {
        TermUnificationResultSpec 
        { .querySigma  = f(a),
          .resultSigma = 1 + a,
          .constraints = { 1 + a != f(a), } },

        TermUnificationResultSpec 
        { .querySigma  = f(a),
          .resultSigma = 1 + num(1),
          .constraints = { f(a) != 1 + num(1), } }, 


        TermUnificationResultSpec 
        { .querySigma  = f(a),
          .resultSigma = f(a),
          .constraints = Stack<Literal*>{} }, 

      }
})

INDEX_TEST(term_indexing_one_side_interp_08, 
    SUGAR(Rat),
    IndexTest {
      .index = getTermIndex(),
      .uwa = Options::UnificationWithAbstraction::ONE_INTERP,
      .fixedPointIteration = false,
      .insert = {
        1 + num(1),
        1 + a,
        a,
        f(x),
      },
      .query = 3 + a,
      .expected =  {
        TermUnificationResultSpec 
        { .querySigma  = 3 + a,
          .resultSigma = 1 + a,
          .constraints = { 1 + a != 3 + a, } },

        TermUnificationResultSpec 
        { .querySigma  = 3 + a,
          .resultSigma = 1 + num(1),
          .constraints = { 3 + a != 1 + num(1), } }, 

        TermUnificationResultSpec 
        { .querySigma  = 3 + a,
          .resultSigma = a,
          .constraints = { 3 + a != a, } }, 

        TermUnificationResultSpec 
        { .querySigma  = 3 + a,
          .resultSigma = f(x),
          .constraints = { 3 + a != f(x) } }, 

      }
})

INDEX_TEST(term_index_floor_1,
    SUGAR(Rat),
    IndexTest {
      .index = getTermIndex(),
      .uwa = Options::UnificationWithAbstraction::ALASCA_MAIN,
      .fixedPointIteration = false,
      .insert = {
        a,
        floor(b),
        floor(f2(floor(x0),floor(x1))),
      },
      .query = floor(f2(floor(x0),floor(x1))),
      .expected = { 

          TermUnificationResultSpec 
          { .querySigma  = floor(f2(floor(x0),floor(x1))),
            .resultSigma = floor(f2(floor(x0),floor(x1))),
            .constraints = noConstraints() }, 

      },
    })


INDEX_TEST(term_index_floor_1_a,
    SUGAR(Rat),
    IndexTest {
      .index = getTermIndex(),
      .uwa = Options::UnificationWithAbstraction::ALASCA_MAIN,
      .fixedPointIteration = false,
      .insert = {
        a,
        floor(b),
        floor(c),
      },
      .query = floor(c),
      .expected = { 

          TermUnificationResultSpec 
          { .querySigma  = floor(c),
            .resultSigma = floor(c),
            .constraints = noConstraints() }, 

      },
    })


TEST_FUN(term_indexing_poly_01)
{
  auto uwa = Options::UnificationWithAbstraction::ONE_INTERP;
  auto fixedPointIteration = false;
  auto index = getTermIndex();

  DECL_DEFAULT_VARS
  DECL_DEFAULT_SORT_VARS  
  NUMBER_SUGAR(Rat)
  DECL_CONST(a, Rat) 
  DECL_POLY_CONST(h, 1, alpha)
  DECL_SORT(A)

  index->insert(tld(1 + a ));
  index->insert(tld(h(Rat)));

  checkTermMatches(*index, uwa, fixedPointIteration, h(alpha), Stack<TermUnificationResultSpec>{

        TermUnificationResultSpec 
        { .querySigma  = h(Rat),
          .resultSigma = h(Rat),
          .constraints = Stack<Literal*>{  } }, 

        TermUnificationResultSpec 
        { .querySigma  = h(Rat),
          .resultSigma = 1 + a,
          .constraints = { 1 + a != h(Rat), } }, 

      });

  checkTermMatches(*index, uwa, fixedPointIteration, h(A), Stack<TermUnificationResultSpec>{ });
}


#define POLY_SUGAR(Rat)                                                                   \
  DECL_DEFAULT_VARS                                                                       \
  DECL_DEFAULT_SORT_VARS                                                                  \
  NUMBER_SUGAR(Rat)                                                                       \
  DECL_POLY_CONST(b, 1, alpha)                                                            \
  DECL_POLY_CONST(a, 1, alpha)                                                            \
  DECL_POLY_FUNC(f, 1, {alpha}, alpha)                                                    \
  DECL_SORT(A)                                                                            \
  DECL_CONST(someA, A)                                                                    \


#define HOL_SUGAR(...)                                                                    \
  DECL_DEFAULT_VARS                                                                       \
  DECL_DEFAULT_SORT_VARS                                                                  \
  NUMBER_SUGAR(Rat)                                                                       \
  DECL_SORT(srt)                                                                          \
  __VA_ARGS__

 


INDEX_TEST(hol_0101,
    HOL_SUGAR(
      DECL_FUNC(f3, {srt, srt, srt}, srt)
      DECL_CONST(f1, arrow(srt, srt))
      DECL_CONST(f2, arrow(srt, srt))
      DECL_CONST(h, arrow(arrow(srt, srt), srt))
    ),
    IndexTest {
      .index = getTermIndexHOL(),
      .uwa = Options::UnificationWithAbstraction::FUNC_EXT,
      .insert = {
               f3(x          , x, ap(h, f1)),
      },
      .query = f3(ap(h, f2), y, y          ),
      .expected =  {

        TermUnificationResultSpec 
        { .querySigma  = f3(ap(h, f2), ap(h, f1), ap(h, f1)),
          .resultSigma = f3(ap(h, f1), ap(h, f1), ap(h, f1)),
          .constraints = { f1 != f2 } }, 

      }
    })


INDEX_TEST(hol_0102,
    HOL_SUGAR(
      DECL_FUNC(f3, {srt, srt, srt}, srt)
      DECL_CONST(f1, arrow(srt, srt))
      DECL_CONST(f2, arrow(srt, srt))
      DECL_CONST(h, arrow(arrow(srt, srt), srt))
    ),
    IndexTest {
      .index = getTermIndexHOL(),
      .uwa = Options::UnificationWithAbstraction::FUNC_EXT,
      .insert = {
               f3(ap(h, f2), y, y          ),
      },
      .query = f3(x          , x, ap(h, f1)),
      .expected =  {

        TermUnificationResultSpec 
        { .querySigma  = f3(ap(h, f1), ap(h, f1), ap(h, f1)),
          .resultSigma = f3(ap(h, f2), ap(h, f1), ap(h, f1)),
          .constraints = { f1 != f2 } }, 

      }
    })




INDEX_TEST(hol_02,
    HOL_SUGAR(
      DECL_FUNC(f3, {srt, srt, srt}, srt)
      DECL_CONST(f1, arrow(srt, srt))
      DECL_CONST(f2, arrow(srt, srt))
      DECL_CONST(a, srt)
      DECL_CONST(h, arrow(arrow(srt, srt), srt))
      ),
    IndexTest {
      .index = getTermIndexHOL(),
      .uwa = Options::UnificationWithAbstraction::FUNC_EXT,
      .insert = {
               f3(a          , x, ap(h, f1)),
               f3(x          , x, ap(h, f1)),
      },
      .query = f3(ap(h, f2), y, y          ),
      .expected =  {

        TermUnificationResultSpec 
        { .querySigma  = f3(ap(h, f2), ap(h, f1), ap(h, f1)),
          .resultSigma = f3(ap(h, f1), ap(h, f1), ap(h, f1)),
          .constraints = { f1 != f2 } }, 

      }
    })


INDEX_TEST(hol_03,
    HOL_SUGAR(
      DECL_FUNC(f3, {srt, srt, srt}, srt)
      DECL_CONST(f1, arrow(srt, srt))
      DECL_CONST(f2, arrow(srt, srt))
      DECL_CONST(h1, arrow(arrow(srt, srt), srt))
      DECL_CONST(h2, arrow(arrow(srt, srt), srt))
    ),
    IndexTest {
      .index = getTermIndexHOL(),
      .uwa = Options::UnificationWithAbstraction::FUNC_EXT,
      .insert = {
               ap(h1, f1),
               ap(h2, f1),
      },
      .query = ap(h1, f2),
      .expected =  {
        TermUnificationResultSpec 
        { .querySigma  = ap(h1, f2),
          .resultSigma = ap(h1, f1),
          .constraints = { f1 != f2 } }, 
      }
    })

#define INDEX_TEST_hol_04(idx, ...)                                                       \
  INDEX_TEST(hol_04_ ## idx,                                                              \
    HOL_SUGAR(                                                                            \
      DECL_FUNC(f3, {srt, srt, srt}, srt)                                                 \
      DECL_POLY_CONST(c1, 1, alpha)                                                       \
      DECL_POLY_CONST(c2, 1, alpha)                                                       \
      DECL_POLY_CONST(h, 2, arrow(alpha, beta))                                           \
    ),                                                                                    \
    IndexTest {                                                                           \
      .index = getTermIndexHOL(),                                                         \
      .uwa = Options::UnificationWithAbstraction::FUNC_EXT,                               \
      .insert = {                                                                         \
               ap(h(arrow(srt, srt), srt), c1(arrow(srt, srt))),                          \
               ap(h(srt            , srt), c1(srt)),                                      \
      },                                                                                  \
      __VA_ARGS__                                                                         \
    })


INDEX_TEST_hol_04(01,
      .query = ap(h(arrow(srt,srt), srt), c1(arrow(srt, srt))),
      .expected =  {
        TermUnificationResultSpec 
        { .querySigma  = ap(h(arrow(srt,srt), srt), c1(arrow(srt, srt))),
          .resultSigma = ap(h(arrow(srt,srt), srt), c1(arrow(srt, srt))),
          .constraints = Stack<Literal*>{} }, 
      }
    )

INDEX_TEST_hol_04(02,
      .query = ap(h(arrow(srt,srt), srt), c2(arrow(srt, srt))),
      .expected =  {
        TermUnificationResultSpec 
        { .querySigma  = ap(h(arrow(srt,srt), srt), c2(arrow(srt, srt))),
          .resultSigma = ap(h(arrow(srt,srt), srt), c1(arrow(srt, srt))),
          .constraints = Stack<Literal*>{ c1(arrow(srt,srt)) != c2(arrow(srt,srt)) } }, 
      }
    )


#define INDEX_TEST_hol_05(idx, ...)                                                       \
  INDEX_TEST(hol_05_ ## idx,                                                              \
    HOL_SUGAR(                                                                            \
      DECL_FUNC(f3, {srt, srt, srt}, srt)                                                 \
      DECL_POLY_CONST(c1, 1, alpha)                                                       \
      DECL_POLY_CONST(c2, 1, alpha)                                                       \
      DECL_POLY_CONST(h, 2, arrow(alpha, beta))                                           \
    ),                                                                                    \
    IndexTest {                                                                           \
      .index = getTermIndexHOL(),                                                         \
      .uwa = Options::UnificationWithAbstraction::FUNC_EXT,                               \
      .insert = {                                                                         \
               ap(h(arrow(srt, srt), srt), c1(arrow(srt, srt))),                          \
               ap(h(srt            , srt), c2(srt)),                                      \
      },                                                                                  \
      __VA_ARGS__                                                                         \
    })


INDEX_TEST_hol_05(01,
      .query = ap(h(arrow(srt,srt), srt), c1(arrow(srt, srt))),
      .expected =  {
        TermUnificationResultSpec 
        { .querySigma  = ap(h(arrow(srt,srt), srt), c1(arrow(srt, srt))),
          .resultSigma = ap(h(arrow(srt,srt), srt), c1(arrow(srt, srt))),
          .constraints = Stack<Literal*>{} }, 
      }
    )

INDEX_TEST_hol_05(02,
      .query = ap(h(arrow(srt,srt), srt), c2(arrow(srt, srt))),
      .expected =  {
        TermUnificationResultSpec 
        { .querySigma  = ap(h(arrow(srt,srt), srt), c2(arrow(srt, srt))),
          .resultSigma = ap(h(arrow(srt,srt), srt), c1(arrow(srt, srt))),
          .constraints = Stack<Literal*>{ c1(arrow(srt,srt)) != c2(arrow(srt,srt)) } }, 
      }
    )

INDEX_TEST(hol_06,
    HOL_SUGAR(
      DECL_SORT_BOOL;
      DECL_SORT(A)
      DECL_CONST(f, arrow(Bool, A))
      DECL_CONST(a, Bool)
      DECL_CONST(b, Bool)
    ),
    IndexTest {
      .index = getTermIndexHOL(),
      .uwa = Options::UnificationWithAbstraction::FUNC_EXT,
      .insert = {
               ap(f, a),
               ap(f, b),
               a,
               b
      },
      .query = ap(f,a),
      .expected =  {

        TermUnificationResultSpec 
        { .querySigma  = ap(f,a),
          .resultSigma = ap(f,a),
          .constraints = Stack<Literal*>{ } }, 

        TermUnificationResultSpec 
        { .querySigma  = ap(f,a),
          .resultSigma = ap(f,b),
          .constraints = { a != b } }, 

      }
    })

INDEX_TEST(term_indexing_poly_uwa_01,
    POLY_SUGAR(Rat),
    IndexTest {
      .index = getTermIndex(),
      .uwa = Options::UnificationWithAbstraction::ONE_INTERP,
      .insert = {
        f(alpha, a(alpha)),
        f(alpha, b(alpha)),
        f(A, someA),
        f(A, a(A)),
      },
      .query = f(Rat, a(Rat) + x),
      .expected =  {

        TermUnificationResultSpec 
        { .querySigma  = f(Rat, a(Rat) + x),
          .resultSigma = f(Rat, a(Rat)),
          .constraints = { a(Rat) != a(Rat) + x } }, 

        TermUnificationResultSpec 
        { .querySigma  = f(Rat, a(Rat) + x),
          .resultSigma = f(Rat, b(Rat)),
          .constraints = { b(Rat) != a(Rat) + x } }, 

      }
    })


TEST_FUN(term_indexing_interp_only)
{
  auto uwa = Options::UnificationWithAbstraction::INTERP_ONLY;
  auto fixedPointIteration = false;
  auto index = getTermIndex();

  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Rat)

  DECL_CONST(a, Rat) 
  DECL_CONST(b, Rat) 

  index->insert(tld(num(1) + num(1)));
  index->insert(tld(1 + a          ));

  checkTermMatches(*index, uwa, fixedPointIteration, b + 2, {

        TermUnificationResultSpec 
        { .querySigma  = b + 2,
          .resultSigma = 1 + a,
          .constraints = { 1 + a != b + 2, } }, 

        TermUnificationResultSpec 
        { .querySigma  = b + 2,
          .resultSigma = 1 + num(1),
          .constraints = { 1 + num(1) != b + 2, } }, 

      });

  index->insert(tld(a));

  checkTermMatches(*index, uwa, fixedPointIteration, b + 2 , {

        TermUnificationResultSpec 
        { .querySigma  = b + 2,
          .resultSigma = 1 + a,
          .constraints = { 1 + a != b + 2, } }, 

        TermUnificationResultSpec 
        { .querySigma  = b + 2,
          .resultSigma = 1 + num(1),
          .constraints = { 1 + num(1) != b + 2, } }, 

      });

}

TEST_FUN(literal_indexing)
{
  auto uwa = Options::UnificationWithAbstraction::ONE_INTERP;
  auto fixedPointIteration = false;
  auto index = getLiteralIndex();

  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Rat)
  DECL_PRED(p, {Rat})

  DECL_CONST(a, Rat) 
  DECL_CONST(b, Rat) 

  Clause* dummy = unit(p(a));

  index->insert(LiteralClause{ p(num(1) + num(1)), dummy });
  index->insert(LiteralClause{ p(1 + a          ), dummy });

  checkLiteralMatches(*index, uwa, fixedPointIteration, p(b + 2), {

      LiteralUnificationResultSpec {
        .querySigma = p(b + 2),
        .resultSigma = p(num(1) + 1),
        .constraints = { b + 2 != num(1) + 1 }, },

      LiteralUnificationResultSpec {
        .querySigma = p(b + 2),
        .resultSigma = p(a + 1),
        .constraints = { b + 2 != a + 1 }, },

      });

  index->insert(LiteralClause{ p(b + 2),unit(p(b + 2)) });
  index->insert(LiteralClause{ p(2 + b),unit(p(2 + b)) });

  checkLiteralMatches(*index, uwa, fixedPointIteration, p(b + 2), {

      LiteralUnificationResultSpec {
        .querySigma = p(b + 2),
        .resultSigma = p(num(1) + 1),
        .constraints = { b + 2 != num(1) + 1 }, },

      LiteralUnificationResultSpec {
        .querySigma = p(b + 2),
        .resultSigma = p(a + 1),
        .constraints = { b + 2 != a + 1 }, },

      LiteralUnificationResultSpec {
        .querySigma = p(b + 2),
        .resultSigma = p(b + 2),
        .constraints = Stack<Literal*>{  }, },

      LiteralUnificationResultSpec {
        .querySigma = p(b + 2),
        .resultSigma = p(b + 2),
        .constraints = Stack<Literal*>{ b + 2 != 2 + b }, },

      });


}

TEST_FUN(higher_order)
{

  DECL_DEFAULT_VARS
  DECL_DEFAULT_SORT_VARS  
  NUMBER_SUGAR(Rat)
  DECL_SORT(srt) 
  DECL_CONST(a, arrow(srt, srt))
  DECL_CONST(b, arrow(srt, srt))
  DECL_CONST(c, srt)  
  DECL_CONST(f, arrow(arrow(srt, srt), srt))
  DECL_CONST(g, arrow(srt, arrow(srt, srt)))
  auto uwa = Options::UnificationWithAbstraction::FUNC_EXT;
  auto fixedPointIteration = false;
  auto index = getTermIndexHOL();

  index->insert(tld(ap(f,a)));

  checkTermMatches(*index, uwa, fixedPointIteration, ap(f,b), Stack<TermUnificationResultSpec>{

        TermUnificationResultSpec 
        { .querySigma  = ap(f,b),
          .resultSigma = ap(f,a),
          .constraints = { a != b, } }, 

      });

  index->insert(tld(ap(g,c)));
  index->insert(tld(g));

  checkTermMatches(*index, uwa, fixedPointIteration, TypedTermList(x, arrow(srt, srt)), Stack<TermUnificationResultSpec>{

        TermUnificationResultSpec 
        { .querySigma  = ap(g,c),
          .resultSigma = ap(g,c),
          .constraints = Stack<Literal*>{} }, 

      });

  checkTermMatches(*index, uwa, fixedPointIteration, ap(f,b), Stack<TermUnificationResultSpec>{

        TermUnificationResultSpec 
        { .querySigma  = ap(f,b),
          .resultSigma = ap(f,a),
          .constraints = { a != b, } }, 

      });



}

TEST_FUN(higher_order2)
{
  auto index = getTermIndexHOL();

  DECL_DEFAULT_VARS
  DECL_DEFAULT_SORT_VARS  
  NUMBER_SUGAR(Rat)
  DECL_SORT(srt) 
  DECL_CONST(a, arrow(srt, srt))
  DECL_CONST(b, arrow(srt, srt))
  DECL_CONST(f, arrow({arrow(srt, srt), arrow(srt, srt)}, srt))

  index->insert(tld(ap(ap(f,a),b)));

}

Option<TermUnificationResultSpec> runRobUnify(bool diffNamespaces, Options::UnificationWithAbstraction opt, bool fixedPointIteration, TermList a, TermList b) {
  // TODO parameter instead of opts
  auto n1 = 0;
  auto n2 = diffNamespaces ? 1 : 0;
  auto au = AbstractingUnifier::unify(a, n1, b, n2, AbstractionOracle(opt), fixedPointIteration);

// Option<TermUnificationResultSpec> runRobUnify(TypedTermList a, TypedTermList b, Options::UnificationWithAbstraction opt, bool fixedPointIteration) {
//   auto au = AbstractingUnifier::unify(a, 0, b, 0, AbstractionOracle(opt), fixedPointIteration);

  if (au) {
    return some(TermUnificationResultSpec { 
     .querySigma  = au->subs().apply(a, n1), 
     .resultSigma = au->subs().apply(b, n2), 
     .constraints = *au->computeConstraintLiterals(),
    });

  } else {
    return {};
  }


}

void checkRobUnify(bool diffNamespaces, Options::UnificationWithAbstraction opt, bool fixedPointIteration, TermList a, TermList b, TermUnificationResultSpec exp)
// void checkRobUnify(TypedTermList a, TypedTermList b, Options::UnificationWithAbstraction opt, bool fixedPointIteration, TermUnificationResultSpec exp)
{
  auto is = runRobUnify(diffNamespaces,opt, fixedPointIteration, a, b);
  if (is.isSome() && is.unwrap() == exp) {
    cout << "[  OK  ] " << a << " unify " << b << endl;
  } else {
    cout << "[ FAIL ] " << a << " unify " << b << endl;
    cout << "is:       " << is << endl;
    cout << "expected: " << exp << endl;
    ASSERTION_VIOLATION
  }
}


void checkRobUnifyFail(bool diffNamespaces, Options::UnificationWithAbstraction opt, bool fixedPointIteration, TermList a, TermList b)
// void checkRobUnifyFail(TypedTermList a, TypedTermList b, Options::UnificationWithAbstraction opt, bool fixedPointIteration)
{
  auto is = runRobUnify(diffNamespaces, opt, fixedPointIteration, a, b);
  if(is.isNone()) {
      cout << "[  OK  ] " << a << " unify " << b << endl;
  } else {
    cout << "[ FAIL ] " << a << " unify " << b << endl;
    cout << "is:       " << is << endl;
    cout << "expected: nothing" << endl;
    ASSERTION_VIOLATION
  }
}

#define ROB_UNIFY_TEST_NAMESPACED_WITH_SUGAR(name, sugar, opt, fixedPointIteration, lhs, rhs, ...)          \
  TEST_FUN(name)                                                                          \
  {                                                                                       \
    __ALLOW_UNUSED(sugar)                                                            \
    checkRobUnify(/* namespaced */ true, opt, fixedPointIteration, lhs, rhs,  __VA_ARGS__ );                                                     \
  }                                                                                       \

#define ROB_UNIFY_TEST_NAMESPACED(name, ...) ROB_UNIFY_TEST_NAMESPACED_WITH_SUGAR(name, SUGAR(Rat), __VA_ARGS__)

#define ROB_UNIFY_TEST(name, sugar, opt, fixedPointIteration, lhs, rhs, ...)              \
  TEST_FUN(name)                                                                          \
  {                                                                                       \
    __ALLOW_UNUSED(sugar)                                                                 \
    checkRobUnify(/* namespaced */ false, opt, fixedPointIteration, lhs, rhs, __VA_ARGS__ );        \
  }                                                                                       \

#define ROB_UNIFY_TEST_FAIL(name, sugar, opt, fixedPointIteration, lhs, rhs)                     \
  TEST_FUN(name)                                                                          \
  {                                                                                       \
    __ALLOW_UNUSED(sugar)                                                            \
    checkRobUnifyFail(false, opt, fixedPointIteration, lhs, rhs);                         \
  }                                                                                       \

#define ROB_UNIFY_TEST_FAIL_NAMESPACED(name, opt, lhs, rhs)                               \
  TEST_FUN(name)                                                                          \
  {                                                                                       \
    SUGAR(Rat)                                                                            \
    checkRobUnifyFail(true, opt, /* fixedPointIteration */ false, lhs, rhs);              \
  }                                                                                       \

ROB_UNIFY_TEST(rob_unif_test_01,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ONE_INTERP,
    /* withFixedPointIteration */ false,
    f(b + 2), 
    f(x + 2),
    TermUnificationResultSpec { 
      .querySigma = f(b + 2),
      .resultSigma = f(x + 2),
      .constraints = { x + 2 != b + 2 },
    })

ROB_UNIFY_TEST(rob_unif_test_02,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ONE_INTERP,
    /* withFixedPointIteration */ false,
    f(b + 2), 
    f(x + 2),
    TermUnificationResultSpec { 
      .querySigma = f(b + 2),
      .resultSigma = f(x + 2),
      .constraints = { x + 2 != b + 2 },
    })

ROB_UNIFY_TEST(rob_unif_test_03,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ONE_INTERP,
    /* withFixedPointIteration */ false,
    f(x + 2), 
    f(a),
    TermUnificationResultSpec { 
      .querySigma = f(x + 2),
      .resultSigma = f(a),
      .constraints = { x + 2 != a },
    })

ROB_UNIFY_TEST_FAIL(rob_unif_test_04,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ONE_INTERP,
    /* withFixedPointIteration */ false,
    f(a), g(1 + a))


ROB_UNIFY_TEST(rob_unif_test_05,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ONE_INTERP,
    /* withFixedPointIteration */ false,
    f(a + b), 
    f(x + y),
    TermUnificationResultSpec { 
      .querySigma = f(a + b),
      .resultSigma = f(x + y),
      .constraints = { x + y != a + b },
    })

ROB_UNIFY_TEST(rob_unif_test_06,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ONE_INTERP,
    /* withFixedPointIteration */ false,
    f2(x, x + 1), 
    f2(a, a),
    TermUnificationResultSpec { 
      .querySigma = f2(a, a + 1),
      .resultSigma = f2(a, a),
      .constraints = { a != a + 1 },
    })



ROB_UNIFY_TEST(alasca3_test_01,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f2(x, a + b + c),
    f2(x, x + b + a),
    TermUnificationResultSpec { 
      .querySigma  = f2(c, a + b + c),
      .resultSigma = f2(c, c + b + a),
      .constraints = Stack<Literal*>{},
    })

ROB_UNIFY_TEST(alasca3_test_02,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f2(a + b + c, f2(x,b)),
    f2(x + y + a, f2(x,y)),
    TermUnificationResultSpec { 
      .querySigma  = f2(a + b + c, f2(c,b)),
      .resultSigma = f2(c + b + a, f2(c,b)),
      .constraints = Stack<Literal*>{},
    })

ROB_UNIFY_TEST(alasca3_test_02_bad,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f2(f2(x,b), a + b + c),
    f2(f2(x,y), x + y + a),
    TermUnificationResultSpec { 
      .querySigma  = f2(f2(c,b), a + b + c),
      .resultSigma = f2(f2(c,b), c + b + a),
      .constraints = Stack<Literal*>{  },
      .alascaSimpl = true,
    })

ROB_UNIFY_TEST(alasca3_test_02_bad_fpi,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ true,
    f2(f2(x,b), a + b + c),
    f2(f2(x,y), x + y + a),
    TermUnificationResultSpec { 
      .querySigma  = f2(f2(c,b), a + b + c),
      .resultSigma = f2(f2(c,b), c + b + a),
      .constraints = Stack<Literal*>{  },
      .alascaSimpl = true,
    })


ROB_UNIFY_TEST(alasca3_test_03,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f2(x, a + b + c),
    f2(x, x + b + a),
    TermUnificationResultSpec { 
      .querySigma  = f2(c, a + b + c),
      .resultSigma = f2(c, c + b + a),
      .constraints = Stack<Literal*>{ },
    })


ROB_UNIFY_TEST(alasca3_test_04,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f2(x, 2 * a + b + c),
    f2(x, x     + b + a),
    TermUnificationResultSpec { 
      .querySigma  = f2(a + c,  2 * a  + b + c),
      .resultSigma = f2(a + c, (a + c) + b + a),
      .constraints = Stack<Literal*>{ },
    })

ROB_UNIFY_TEST(alasca3_test_05,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f2(x, 2 * a + b + c),
    f2(x, x     + b + y),
    TermUnificationResultSpec { 
      .querySigma  = f2(2 * a - x0 + c,  2 * a + b + c),
      .resultSigma = f2(2 * a - x0 + c,  2 * a + b + c),
      .constraints = Stack<Literal*>{  },
      .alascaSimpl = true,
    })


// ROB_UNIFY_TEST(alasca3_test_06,
//     SUGAR(Rat),
//     Options::UnificationWithAbstraction::ALASCA_MAIN,
//     /* fixedPointIteration */ false,
//     f2(x, 2 * a +             b + c),
//     f2(x, x     + frac(1,2) * b + y),
//     TermUnificationResultSpec { 
//       .querySigma  = f2(x, 2 * a +             b + c),
//       .resultSigma = f2(x, x     + frac(1,2) * b + y),
//       .constraints = Stack<Literal*>{ x + y != 2 * a + frac(1,2) * b + c },
//     })


ROB_UNIFY_TEST(alasca3_test_06,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f2(x, 2 * a +             b + c),
    f2(x, x     + frac(1,2) * b + y),
    TermUnificationResultSpec { 
      .querySigma  = f2(-x + 2 * a + frac(1,2) * b + c, 2 * a + b + c),
      .resultSigma = f2(-x + 2 * a + frac(1,2) * b + c, 2 * a + b + c),
      .constraints = Stack<Literal*>{  },
      .alascaSimpl = true,
    })


ROB_UNIFY_TEST(alasca3_test_07,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f2(x, f(x) + y),
    f2(x, f(y) + y),
    TermUnificationResultSpec { 
      .querySigma  = f2(x, f(x) + x),
      .resultSigma = f2(x, f(x) + x),
      .constraints = Stack<Literal*>{},
    })


ROB_UNIFY_TEST_FAIL(alasca3_test_08,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f2(x, a + b),
    f2(x, c + b))

ROB_UNIFY_TEST_FAIL(alasca3_test_09,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f2(x, f(a) + b),
    f2(x, f(y) + g(y)))


ROB_UNIFY_TEST(alasca3_test_10,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f2(x, a + b + x),
    f2(x, c + b),
    TermUnificationResultSpec { 
      .querySigma  = f2(-a + c, a + b + (-a + c)),
      .resultSigma = f2(-a + c, c + b),
      .constraints = Stack<Literal*>{},
    })

ROB_UNIFY_TEST_FAIL(alasca3_test_11,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f2(x, f(a) +  2 * g(a)),
    f2(x, frac(1,2) * f(a) + g(x) + g(y)))

ROB_UNIFY_TEST_FAIL(alasca3_test_12,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f2(x, f(x) + f(b) + f(z)),
    f2(x, f(a) - f(y)))

ROB_UNIFY_TEST_FAIL(alasca3_test_13,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f2(x, f(x)),
    f2(x, f(a) - f(y)))

ROB_UNIFY_TEST(alasca3_test_14,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f2(x, 0),
    f2(x, f(a) - f(y)),
    TermUnificationResultSpec { 
      .querySigma  = f2(x, 0),
      .resultSigma = f2(x, f(a) - f(a)),
      .constraints = Stack<Literal*>{},
    })

ROB_UNIFY_TEST(alasca3_test_15,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f2(x, 2 * (a + b)),
    f2(x, x  + 2 * b +  2 * a),
    TermUnificationResultSpec { 
      .querySigma  = f2(0, 2 * (a + b)),
      .resultSigma = f2(0, 0 + 2 * a  + 2 * b ),
      .constraints = Stack<Literal*>{ },
    })

ROB_UNIFY_TEST(alasca_main_test_16,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    2 * f(x),
    2 * f(y),
    TermUnificationResultSpec { 
      .querySigma  = 2 * f(x),
      .resultSigma = 2 * f(x),
      .constraints = Stack<Literal*>{ },
    })

ROB_UNIFY_TEST(alasca_main_test_17,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    2 * f(x),
    f(y) + f(z),
    TermUnificationResultSpec { 
      .querySigma  = 2 * f(x),
      .resultSigma = f(x) + f(x),
      .constraints = Stack<Literal*>{ },
    })

ROB_UNIFY_TEST_FAIL(alasca_main_test_18,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    2 * f(x),
    f(y) + frac(1,2) *  f(z))

ROB_UNIFY_TEST(alasca_main_test_19,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    2 * f(x) - f(y) - f(z),
    num(0),
    TermUnificationResultSpec { 
      .querySigma  = 2 * f(x) - f(x) - f(x),
      .resultSigma = num(0),
      .constraints = Stack<Literal*>{ },
    })

ROB_UNIFY_TEST(alasca_main_test_20,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    -2 * f(x) + f(y) + f(z),
    num(0),
    TermUnificationResultSpec { 
      .querySigma  = -2 * f(x) + f(x) + f(x),
      .resultSigma = num(0),
      .constraints = Stack<Literal*>{ },
    })

ROB_UNIFY_TEST(alasca_main_test_21,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f(x) + f(y),
    f(a) + f(b),
    TermUnificationResultSpec { 
      .querySigma  = f(x) + f(y),
      .resultSigma = f(a) + f(b),
      .constraints = { f(a) + f(b) != f(x) + f(y) },
    })

ROB_UNIFY_TEST(alasca_main_test_22,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ true,
    f(x) + f(y) + g(x),
    f(a) + f(b) + g(a),
    TermUnificationResultSpec { 
      .querySigma  = f(a) + f(b) + g(a),
      .resultSigma = f(a) + f(b) + g(a),
      .constraints = Stack<Literal*>{},
    })

ROB_UNIFY_TEST(constr_var_01,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    s2r(x),
    s2r(r2s(s2r(x) + y)),
    TermUnificationResultSpec { 
      .querySigma  = s2r(x),
      .resultSigma = s2r(r2s(s2r(x) + y)),
      .constraints = Stack<Literal*>{x != r2s(s2r(x) + y)},
    })


INDEX_TEST(top_level_constraints_2,
    SUGAR(Rat),
    IndexTest {
      .index = getTermIndex(),
      .uwa = Options::UnificationWithAbstraction::ALASCA_CAN_ABSTRACT,
      .fixedPointIteration = false,
      .insert = {
        a + b + c,
        a + b + a + c,
      },
      .query = a + y + x,
      .expected = { 

          TermUnificationResultSpec 
          { .querySigma  = a + x0 + x1,
            .resultSigma = a + b + c,
            .constraints = Stack<Literal*>{ a + b + c != a + x1 + x0 } }, 

          TermUnificationResultSpec 
          { .querySigma  = a + x0 + x1,
            .resultSigma = a + b + a + c,
            .constraints = Stack<Literal*>{ a + b + a + c != a + x1 + x0 } }, 

      },
    })

INDEX_TEST(bug02,
    SUGAR(Rat),
    IndexTest {
      .index = getTermIndex(),
      .uwa = Options::UnificationWithAbstraction::ONE_INTERP,
      .insert = {
        f2(y, x),
      },
      .query = f2(a, b),
      .expected = { 

          TermUnificationResultSpec 
          { .querySigma  = f2(a,b),
            .resultSigma = f2(a,b),
            .constraints = noConstraints() }, 

      },
    })

ROB_UNIFY_TEST(alasca_main_test_01,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f2(x, a + b + c),
    f2(x, x + b + a),
    TermUnificationResultSpec { 
      .querySigma  = f2(c, a + b + c),
      .resultSigma = f2(c, c + b + a),
      .constraints = Stack<Literal*>{},
    })

ROB_UNIFY_TEST(alasca_main_test_02,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f2(a + b + c, f2(x,b)),
    f2(x + y + a, f2(x,y)),
    TermUnificationResultSpec { 
      .querySigma  = f2(a + b + c, f2(c,b)),
      .resultSigma = f2(c + b + a, f2(c,b)),
      .constraints = Stack<Literal*>{},
    })

ROB_UNIFY_TEST(alasca_main_test_02_bad,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f2(f2(x,b), a + b + c),
    f2(f2(x,y), x + y + a),
    TermUnificationResultSpec { 
      .querySigma  = f2(f2(-b + c + b,b), a + b + c),
      .resultSigma = f2(f2(-b + c + b,b), -b + c + b + b + a),
      .constraints = Stack<Literal*>{},
    })

ROB_UNIFY_TEST(alasca_main_test_02_bad_fpi,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ true,
    f2(f2(x,b), a + b + c),
    f2(f2(x,y), x + y + a),
    TermUnificationResultSpec { 
      .querySigma  = f2(f2(-b + c + b,b), a + b + c),
      .resultSigma = f2(f2(-b + c + b,b), -b + c + b + b + a),
      .constraints = Stack<Literal*>{},
    })


ROB_UNIFY_TEST(alasca_main_test_03,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f2(x, a + b + c),
    f2(x, x + b + a),
    TermUnificationResultSpec { 
      .querySigma  = f2(c, a + b + c),
      .resultSigma = f2(c, c + b + a),
      .constraints = Stack<Literal*>{ },
    })


ROB_UNIFY_TEST(alasca_main_test_04,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f2(x, 2 * a + b + c),
    f2(x, x     + b + a),
    TermUnificationResultSpec { 
      .querySigma  = f2(a + c,  2 * a  + b + c),
      .resultSigma = f2(a + c, (a + c) + b + a),
      .constraints = Stack<Literal*>{ },
    })


ROB_UNIFY_TEST(alasca_main_test_05,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f2(x, 2 * a + b + c),
    f2(x, x     + b + y),
    TermUnificationResultSpec { 
      .querySigma  = f2(2 * a + c - x,  2 * a          + b + c),
      .resultSigma = f2(2 * a + c - x,  2 * a + c - x  + b + x),
      .constraints = Stack<Literal*>{},
    })


ROB_UNIFY_TEST(alasca_main_test_06,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f2(x, b),
    f2(x, frac(1,2) * b + x + y),
    TermUnificationResultSpec { 
      .querySigma  = f2(frac(1,2) * b - x, b),
      .resultSigma = f2(frac(1,2) * b - x, frac(1,2) * b - x  + frac(1,2) * b + x),
      .constraints = Stack<Literal*>{ },
    })


ROB_UNIFY_TEST(alasca_main_test_07,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f2(x, f(x) + y),
    f2(x, f(y) + y),
    TermUnificationResultSpec { 
      .querySigma  = f2(x, f(x) + x),
      .resultSigma = f2(x, f(x) + x),
      .constraints = Stack<Literal*>{},
    })


ROB_UNIFY_TEST_FAIL(alasca_main_test_08,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f2(x, a + b),
    f2(x, c + b))

ROB_UNIFY_TEST_FAIL(alasca_main_test_09,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f2(x, f(a) + b),
    f2(x, f(y) + g(y)))


ROB_UNIFY_TEST(alasca_main_test_10,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f2(x, a + b + x),
    f2(x, c + b),
    TermUnificationResultSpec { 
      .querySigma  = f2(-a + c, a + b + (-a + c)),
      .resultSigma = f2(-a + c, c + b),
      .constraints = Stack<Literal*>{},
    })

ROB_UNIFY_TEST_FAIL(alasca_main_test_11,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f2(x, f(a) +  2 * g(a)),
    f2(x, frac(1,2) * f(a) + g(x) + g(y)))

ROB_UNIFY_TEST_FAIL(alasca_main_test_12,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f2(x, f(x) + f(b) + f(z)),
    f2(x, f(a) - f(y)))

ROB_UNIFY_TEST_FAIL(alasca_main_test_13,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f2(x, f(x)),
    f2(x, f(a) - f(y)))

ROB_UNIFY_TEST(alasca_main_test_14,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f2(x, 0),
    f2(x, f(a) - f(y)),
    TermUnificationResultSpec { 
      .querySigma  = f2(x, 0),
      .resultSigma = f2(x, f(a) - f(a)),
      .constraints = Stack<Literal*>{},
    })

ROB_UNIFY_TEST(alasca_main_test_15,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f2(x, 2 * (a + b)),
    f2(x, x  + 2 * b +  2 * a),
    TermUnificationResultSpec { 
      .querySigma  = f2(0, 2 * (a + b)),
      .resultSigma = f2(0, 0 + 2 * a  + 2 * b ),
      .constraints = Stack<Literal*>{ },
    })

ROB_UNIFY_TEST(alasca_main_constr_var_01,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    s2r(x),
    s2r(r2s(s2r(x) + y)),
    TermUnificationResultSpec { 
      .querySigma  = s2r(x),
      .resultSigma = s2r(r2s(s2r(x) + y)),
      .constraints = Stack<Literal*>{x != r2s(s2r(x) + y)},
    })


ROB_UNIFY_TEST(alasca3_constr_var_02,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    x,
    f(x + f(y)),
    TermUnificationResultSpec { 
      .querySigma  = x,
      .resultSigma = f(x + f(y)),
      .constraints = { x != f(x + f(y)) },
    })


ROB_UNIFY_TEST(alasca_main_constr_var_03,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    x,
    f(y + f(x)),
    TermUnificationResultSpec { 
      .querySigma  = x,
      .resultSigma = f(y + f(x)),
      .constraints = { x != f(y + f(x)) },
    })

ROB_UNIFY_TEST_FAIL(alasca_main_constr_var_04,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    x,
    f(f(x)))

ROB_UNIFY_TEST_FAIL(alasca_main_constr_var_05,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    x,
    f2(x, y + f(x))
  )

ROB_UNIFY_TEST_FAIL(alasca_main_constr_var_06,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    x,
    f2(y + f(x), x)
  )

ROB_UNIFY_TEST_FAIL(alasca_main_constr_var_07,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    x,
    f2(f(x), x)
  )

ROB_UNIFY_TEST(alasca_main_constr_var_08,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    x,
    f2(y + f(x), y + f(x)),
    TermUnificationResultSpec { 
      .querySigma  = x,
      .resultSigma = f2(y + f(x), y + f(x)),
      .constraints = { x != f2(y + f(x), y + f(x)) },
    })

ROB_UNIFY_TEST(alasca_main_constr_var_09,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    x,
    f2(f(y) + x, y + f(x)),
    TermUnificationResultSpec { 
      .querySigma  = x,
      .resultSigma = f2(f(y) + x, y + f(x)),
      .constraints = { x != f2(f(y) + x, y + f(x)) },
    })


// TODO this requires non-linear multiplication unification which we don't support rn
// ROB_UNIFY_TEST(alasca_main_constr_var_10,
//     SUGAR(Rat),
//     Options::UnificationWithAbstraction::ALASCA_MAIN,
//     /* fixedPointIteration */ false,
//     f2(x, y),
//     f2(y * x, 0),
//     TermUnificationResultSpec { 
//       .querySigma  = f2(0    , 0),
//       .resultSigma = f2(num(0) * 0, 0),
//       .constraints = Stack<Literal*>{ },
//     })
//
//
// ROB_UNIFY_TEST(alasca_main_constr_var_11,
//     SUGAR(Rat),
//     Options::UnificationWithAbstraction::ALASCA_MAIN,
//     /* fixedPointIteration */ false,
//     f2(x, y),
//     f2(x * y, 0),
//     TermUnificationResultSpec { 
//       .querySigma  = f2(0    , 0),
//       .resultSigma = f2(num(0) * 0, 0),
//       .constraints = Stack<Literal*>{ },
//     })

ROB_UNIFY_TEST_FAIL(alasca_main_misc02,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f2(2 * f(x) + g(a), f2(x, y)),
    f2(f(a) + f(b) + g(x), f2(x, y))
    )
    

ROB_UNIFY_TEST_FAIL(alasca_main_misc03,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f2(2 * f(x) + g(a), f2(x, y)),
    f2(f(a) + f(a) + g(b), f2(x, y))
    )

ROB_UNIFY_TEST(alasca_main_misc04,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f2(2 * f(x) + g(b), f2(x, y)),
    f2(f(a) + f(a) + g(y), f2(x, y)),
    TermUnificationResultSpec { 
      .querySigma  = f2(2 * f(a) + g(b), f2(a, b)),
      .resultSigma = f2(f(a) + f(a) + g(b), f2(a, b)),
      .constraints = Stack<Literal*>{ },
    })

ROB_UNIFY_TEST(alasca_main_misc05,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f2(2 * f(x) + g(a), f2(x, y)),
    f2(f(a) + f(y) + g(y), f2(x, y)),
    TermUnificationResultSpec { 
      .querySigma  = f2(2 * f(a) + g(a), f2(a, a)),
      .resultSigma = f2(f(a) + f(a) + g(a), f2(a, a)),
      .constraints = Stack<Literal*>{ },
    })

ROB_UNIFY_TEST_FAIL(alasca_main_misc06,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f2(2 * f(x) + g(b), f2(x, y)),
    f2(f(a) + f(a) + g(x), f2(x, y)))

ROB_UNIFY_TEST_FAIL(alasca_main_misc07,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f2(2 * f(x) + g(b)       , f2(x, y)),
    f2(f(a) + f(a) + 2 * g(x), f2(x, y))
    )

ROB_UNIFY_TEST_FAIL(alasca_main_misc08,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f2(2 * f(x) + g(b)        , f2(x, y)),
    f2(f(a) + f(a) + -2 * g(x), f2(x, y))
    )

// TODO requires non-linear reasoning
// ROB_UNIFY_TEST_FAIL(alasca_main_non_normalized_mul_01,
//     SUGAR(Rat),
//     Options::UnificationWithAbstraction::ALASCA_MAIN,
//     /* fixedPointIteration */ false,
//     f2(x * a * y, f2(x, y)),
//     f2(5 * a    , f2(2, 3)))
//
// ROB_UNIFY_TEST(alasca_main_non_normalized_mul_02,
//     SUGAR(Rat),
//     Options::UnificationWithAbstraction::ALASCA_MAIN,
//     /* fixedPointIteration */ false,
//     f2(x * a * y, f2(x, y)),
//     f2(6 * a    , f2(2, 3)),
//     TermUnificationResultSpec { 
//       .querySigma  = f2(2 * a * 3, f2(2,3)),
//       .resultSigma = f2(6 * a    , f2(2,3)),
//       .constraints = Stack<Literal*>{ },
//     })

// TODO?
// ROB_UNIFY_TEST_FAIL(alasca_main_constr_var_12,
//     Options::UnificationWithAbstraction::ALASCA_MAIN,
//     f2(x, y),
//     f2(y * x, 5))
//
// ROB_UNIFY_TEST_FAIL(alasca_main_constr_var_13,
//     Options::UnificationWithAbstraction::ALASCA_MAIN,
//     f2(x, y),
//     f2(x * y, 5))
//
// ROB_UNIFY_TEST_FAIL(alasca_main_constr_var_14,
//     Options::UnificationWithAbstraction::ALASCA_MAIN,
//     x,
//     f(x) + g(x))



ROB_UNIFY_TEST(alasca_better_normalization_01,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f(x + y) + f(y + x),
    f(x + y) + f(x + y),
    TermUnificationResultSpec { 
      .querySigma  = f(x + y) + f(y + x),
      .resultSigma = f(x + y) + f(x + y),
      .constraints = Stack<Literal*>{ },
    })

ROB_UNIFY_TEST(alasca_better_normalization_02,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f(x + 0) + f(0 + x),
    f(b + a) + f(a + b),
    TermUnificationResultSpec { 
      .querySigma  = 2 * f(a + b),
      .resultSigma = 2 * f(a + b),
      .constraints = Stack<Literal*>{ },
      .alascaSimpl = true,
    })

ROB_UNIFY_TEST_FAIL(alasca_better_normalization_03,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f(c + f(x)) + f(c + f(x)),
    f(b + f(a)) + f(f(a) + b))

ROB_UNIFY_TEST(alasca_main_bug01,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f2(x - y, f2(x, y)),
    f2(0    , f2(x, y)),
    TermUnificationResultSpec { 
      .querySigma  = f2(x - x, f2(x,x)),
      .resultSigma = f2(0    , f2(x,x)),
      .constraints = Stack<Literal*>{ },
    })


ROB_UNIFY_TEST(alasca_main_non_linear_mul_1,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f(3 * a),
    f(x * a),
    TermUnificationResultSpec { 
      .querySigma  = f(3 * a),
      .resultSigma = f(x * a),
      .constraints = Stack<Literal*>{ 3 * a != x * a },
    })


// TODO requires non-linear reasnoning
// ROB_UNIFY_TEST_FAIL(alasca_main_non_linear_mul_2,
//     SUGAR(Rat),
//     Options::UnificationWithAbstraction::ALASCA_MAIN,
//     /* fixedPointIteration */ false,
//     f2(3 * a, 2),
//     f2(x * a, x))
//
//
// ROB_UNIFY_TEST(alasca_main_non_linear_mul_3_bad,
//     SUGAR(Rat),
//     Options::UnificationWithAbstraction::ALASCA_MAIN,
//     /* fixedPointIteration */ false,
//     f2(2, 3 * a),
//     f2(x, x * a),
//     TermUnificationResultSpec { 
//       .querySigma  = f2(2, 3 * a),
//       .resultSigma = f2(2, 2 * a),
//       .constraints = Stack<Literal*>{ 3 * a != 2 * a },
//     })
//
// ROB_UNIFY_TEST_FAIL(alasca_main_non_linear_mul_3_bad_fpi,
//     SUGAR(Rat),
//     Options::UnificationWithAbstraction::ALASCA_MAIN,
//     /* fixedPointIteration */ true,
//     f2(2, 3 * a),
//     f2(x, x * a))

ROB_UNIFY_TEST_NAMESPACED(alasca_main_namespace_bug_01,
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f2(x    , x    ),
    f2(x + y, x + z),
    TermUnificationResultSpec { 
      .querySigma  = f2(x + y, x + y),
      .resultSigma = f2(x + y, x + y),
      .constraints = Stack<Literal*>{ },
    })

ROB_UNIFY_TEST(alasca_main_misc01,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f2(f2(a + b + c + f(a), x    ), y),
    f2(f2(x + y           , a + c), b + f(a)),
    TermUnificationResultSpec { 
      .querySigma  = f2(f2(a + b + c + f(a), a + c), b + f(a)),
      .resultSigma = f2(f2(a + b + c + f(a), a + c), b + f(a)),
      .constraints = Stack<Literal*>{ },
    })


ROB_UNIFY_TEST(alasca_main_bug03,
    SUGAR(Rat),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    f2(f(y), f2(f(g(a)), f2(-S2, h((-f(g(a)) + f(x)))))),
    f2(S3  , f2(S2     , f2(S4 , h(S4 + S3)))),
    TermUnificationResultSpec { 
      .querySigma = f2(f(x), f2(f(g(a)), f2(-f(g(a)), h((-f(g(a)) + f(x)))))),
      .resultSigma = f2(f(x), f2(f(g(a)), f2(-f(g(a)), h((-f(g(a)) + f(x)))))),
      .constraints = Stack<Literal*>{ },
      .alascaSimpl = true,
    })


ROB_UNIFY_TEST_NAMESPACED(alasca_main_lhs_var_test_namespaces_1,
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    x.sort(Rat),
    f(x),
    TermUnificationResultSpec { 
      .querySigma = f(x),
      .resultSigma = f(x),
      .constraints = Stack<Literal*>{ },
    })

TermList binList(FuncSugar f2, Stack<TermList> ts) 
{
  return arrayIter(std::move(ts))
      .fold([&](auto l, auto r) { return f2(r, l); })
      .unwrap();
}

INDEX_TEST(bug_wrong_ouptut_var_01,
    SUGAR(Rat),
    IndexTest {
      .index = getTermIndex(),
      .uwa = Options::UnificationWithAbstraction::ALASCA_MAIN,
      .fixedPointIteration = true,
      .insert = {
        (2 * f(x0)),
        (3 * b),
      },
      .query = 2 * f(x0),
      .expected = { 

          TermUnificationResultSpec 
          { .querySigma  = 2 * f(x0),
            .resultSigma = 2 * f(x0),
            .constraints = noConstraints() }, 

      },
    })


INDEX_TEST(test_split_num_muls_1,
    SUGAR(Rat),
    IndexTest {
      .index = getTermIndex(),
      .uwa = Options::UnificationWithAbstraction::ALASCA_MAIN,
      .fixedPointIteration = true,
      .insert = {
        (2 * (3 * f(x0))),
        (2 * a),
        (2 * (3 * b)),
      },
      .query = 6 * f(x0),
      .expected = { 

          TermUnificationResultSpec 
          { .querySigma  = 6 * f(x0),
            .resultSigma = 2 * (3 * f(x0)) ,
            .constraints = noConstraints() }, 

      },
    })

INDEX_TEST(test_split_num_muls_2,
    SUGAR(Rat),
    IndexTest {
      .index = getTermIndex(),
      .uwa = Options::UnificationWithAbstraction::ALASCA_MAIN,
      .fixedPointIteration = true,
      .insert = {
        (2 * (3 * f(x0))),
        (2 * a),
        (2 * (3 * b)),
      },
      .query = 2 * (3 * f(x0)),
      .expected = { 

          TermUnificationResultSpec 
          { .querySigma  = 2 * (3 * f(x0)) ,
            .resultSigma = 2 * (3 * f(x0)) ,
            .constraints = noConstraints() }, 

      },
    })


INDEX_TEST(test_split_num_muls_3,
    SUGAR(Rat),
    IndexTest {
      .index = getTermIndex(),
      .uwa = Options::UnificationWithAbstraction::ALASCA_MAIN,
      .fixedPointIteration = true,
      .insert = {
        (2 * (3 * f(x0))),
        (2 * a),
        (2 * (3 * b)),
      },
      .query = 3 * (2 * f(x0)),
      .expected = { 

          TermUnificationResultSpec 
          { .querySigma  = 3 * (2 * f(x0)) ,
            .resultSigma = 2 * (3 * f(x0)) ,
            .constraints = noConstraints() }, 

      },
    })


INDEX_TEST(bug_linear_mul_1,
    SUGAR(Rat),
    IndexTest {
      .index = getTermIndex(),
      .uwa = Options::UnificationWithAbstraction::ALASCA_MAIN_FLOOR,
      .fixedPointIteration = true,
      .insert = {
        floor(2 * a),
        floor(3 * a),
      },
      .query = floor(2 * a),
      .expected = { 
          TermUnificationResultSpec 
          { .querySigma  = floor(2 * a),
            .resultSigma = floor(2 * a),
            .constraints = noConstraints() }, 
      },
    })

INDEX_TEST(bug_linear_mul_2,
    SUGAR(Rat),
    IndexTest {
      .index = getTermIndex(),
      .uwa = Options::UnificationWithAbstraction::ALASCA_MAIN_FLOOR,
      .fixedPointIteration = true,
      .insert = {
        floor(2 * a),
        floor(2 * b),
      },
      .query = floor(2 * a),
      .expected = { 
          TermUnificationResultSpec 
          { .querySigma  = floor(2 * a),
            .resultSigma = floor(2 * a),
            .constraints = noConstraints() }, 
      },
    })

ROB_UNIFY_TEST(alasca_main_int_bug01,
    SUGAR(Int),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    -x,
    a + y + -f(y),
    TermUnificationResultSpec { 
      .querySigma  = -(-(a + x + -f(x))),
      .resultSigma = a + x + -f(x),
      .constraints = Stack<Literal*>{ },
      .alascaSimpl = true,
    })

ROB_UNIFY_TEST(alasca_main_int_bug02,
    SUGAR(Int),
    Options::UnificationWithAbstraction::ALASCA_MAIN,
    /* fixedPointIteration */ false,
    2 * x,
    a + y + -f(y),
    TermUnificationResultSpec { 
      .querySigma  = 2 * x,
      .resultSigma = a + y + -f(y),
      .constraints = { 2 * x != a + y + -f(y)  },
      // .alascaSimpl = true,
    })


ROB_UNIFY_TEST(floor_test_1,
    SUGAR(Real),
    Options::UnificationWithAbstraction::ALASCA_MAIN_FLOOR,
    /* fixedPointIteration */ false,
    f(num(1234)),
    f(floor(x)),
    TermUnificationResultSpec { 
      .querySigma  = f(num(1234)),
      .resultSigma = f(floor(num(1234))),
      .constraints = noConstraints(),
      // .alascaSimpl = true,
    })

ROB_UNIFY_TEST(floor_test_2,
    SUGAR(Real),
    Options::UnificationWithAbstraction::ALASCA_MAIN_FLOOR,
    /* fixedPointIteration */ false,
    f(floor(a) + floor(b)),
    f(floor(x)),
    TermUnificationResultSpec { 
      .querySigma  = f(floor(a) + floor(b)),
      .resultSigma = f(floor(x)),
      // TODO options here: x -> { ⌊a⌋ + ⌊b⌋ , a  + ⌊b⌋ , ⌊a⌋ +  b  }
      .constraints = constraints( floor(a) + floor(b) != floor(x) ),
      .alascaSimpl = true,
    })


ROB_UNIFY_TEST(floor_test_3,
    SUGAR(Real),
    Options::UnificationWithAbstraction::ALASCA_MAIN_FLOOR,
    /* fixedPointIteration */ false,
    f(floor(a) + num(1)),
    f(floor(x)),
    TermUnificationResultSpec { 
      .querySigma  = f(floor(a) + num(1)),
      .resultSigma = f(floor(x)),
      // TODO options here:  x -> { ⌊a⌋ + 1,  a + 1 }
      .constraints = constraints(floor(x) != floor(a) + 1),
      .alascaSimpl = true,
    })

ROB_UNIFY_TEST(floor_test_4,
    SUGAR(Real),
    Options::UnificationWithAbstraction::ALASCA_MAIN_FLOOR,
    /* fixedPointIteration */ false,
    f(floor(a) + frac(1,2)),
    f(floor(x) + frac(1,2)),
    TermUnificationResultSpec { 
      .querySigma  = f(floor(a) + frac(1,2)),
      .resultSigma = f(floor(x) + frac(1,2)),
      // TODO options here: x ->  { a, ⌊a⌋ } 
      .constraints = constraints( floor(x) != floor(a) ),
      .alascaSimpl = true,
    })


ROB_UNIFY_TEST_FAIL(floor_test_6,
    SUGAR(Real),
    Options::UnificationWithAbstraction::ALASCA_MAIN_FLOOR,
    /* fixedPointIteration */ false,
    f(frac(1,2)),
    f(floor(x)))


ROB_UNIFY_TEST(floor_test_7,
    SUGAR(Real),
    Options::UnificationWithAbstraction::ALASCA_MAIN_FLOOR,
    /* fixedPointIteration */ false,
    f(floor(x)),
    f(x),
    TermUnificationResultSpec { 
      .querySigma  = f(floor(x)),
      .resultSigma = f(x),
      .constraints = constraints(x != floor(x)),
      .alascaSimpl = true,
    })

ROB_UNIFY_TEST(floor_test_8,
    SUGAR(Real),
    Options::UnificationWithAbstraction::ALASCA_MAIN_FLOOR,
    /* fixedPointIteration */ false,
    f(floor(x)),
    f(x + floor(a)),
    TermUnificationResultSpec { 
      .querySigma  = f(floor(x)),
      .resultSigma = f(x + floor(a)),
      .constraints = constraints(floor(x) != x + floor(a)),
      .alascaSimpl = true,
    })

ROB_UNIFY_TEST(floor_test_9,
    SUGAR(Real),
    Options::UnificationWithAbstraction::ALASCA_MAIN_FLOOR,
    /* fixedPointIteration */ false,
    f(floor(x) + a),
    f(x),
    TermUnificationResultSpec { 
      .querySigma  = f(floor(x) + a),
      .resultSigma = f(x),
      .constraints = Stack<Literal*>{ floor(x) + a != x },
      .alascaSimpl = true,
    })

ROB_UNIFY_TEST(floor_test_10,
    SUGAR(Real),
    Options::UnificationWithAbstraction::ALASCA_MAIN_FLOOR,
    /* fixedPointIteration */ false,
    f(frac(1,2) * floor(x)),
    f(frac(1,2) * floor(a)),
    TermUnificationResultSpec { 
      .querySigma  = f(frac(1,2) * floor(x)),
      .resultSigma = f(frac(1,2) * floor(a)),
      // TODO options here: x ->  { a, ⌊a⌋ } 
      .constraints = constraints(frac(1,2) * floor(x) != frac(1,2) * floor(a) ),
      .alascaSimpl = true,
    })

ROB_UNIFY_TEST(floor_test_11,
    SUGAR(Real),
    Options::UnificationWithAbstraction::ALASCA_MAIN_FLOOR,
    /* fixedPointIteration */ false,
    f(frac(1,2) * floor(x)),
    f(frac(1,2) * floor(a) + frac(1,2)),
    TermUnificationResultSpec { 
      .querySigma  = f(frac(1,2) * floor(x)),
      .resultSigma = f(frac(1,2) * floor(a) + frac(1,2)),
      // TODO options here: x -> { a + 1 , ⌊a⌋ + 1 }
      .constraints = constraints( frac(1,2) * floor(x) != frac(1,2) * floor(a) + frac(1,2) ),
      .alascaSimpl = true,
    })

ROB_UNIFY_TEST(floor_test_12,
    SUGAR(Real),
    Options::UnificationWithAbstraction::ALASCA_MAIN_FLOOR,
    /* fixedPointIteration */ false,
    f(x0) + f(x1),
    f(x2) + f(x3),
    TermUnificationResultSpec { 
      .querySigma  = f(x0) + f(x1),
      .resultSigma = f(x2) + f(x3),
      .constraints = constraints(f(x0) + f(x1) - f(x2) - f(x3) != 0),
      .alascaSimpl = true,
    })

ROB_UNIFY_TEST_NAMESPACED_WITH_SUGAR(floor_test_14,
    SUGAR(Real),
    Options::UnificationWithAbstraction::ALASCA_MAIN_FLOOR,
    /* fixedPointIteration */ false,
    f(a + b),
    f(b + a),
    TermUnificationResultSpec { 
      .querySigma  = f(a + b),
      .resultSigma = f(b + a),
      .constraints = Stack<Literal*>{},
      // .alascaSimpl = true,
    })

ROB_UNIFY_TEST_NAMESPACED_WITH_SUGAR(floor_test_15,
    SUGAR(Real),
    Options::UnificationWithAbstraction::ALASCA_MAIN_FLOOR,
    /* fixedPointIteration */ false,
    floor(f(x)),
    floor(f(x)),
    TermUnificationResultSpec { 
      .querySigma  = floor(f(x)),
      .resultSigma = floor(f(x)),
      .constraints = noConstraints()
      // .alascaSimpl = true,
    })

ROB_UNIFY_TEST_FAIL(floor_test_16,
    SUGAR(Real),
    Options::UnificationWithAbstraction::ALASCA_MAIN_FLOOR,
    /* fixedPointIteration */ false,
    a - floor(-a),
    num(0))


TEST_FUN(bug05) {
  for (auto mode : {
      Options::UnificationWithAbstraction::ALASCA_MAIN_FLOOR
      }) {
    auto uwa = AbstractingUnifier::empty(AbstractionOracle(mode));
    NUMBER_SUGAR(Rat)
    DECL_DEFAULT_VARS
    DECL_DEFAULT_SORT_VARS
    DECL_POLY_CONST(a, 1, alpha)
    DECL_CONST(b, Rat)

    uwa.unify(x, 2, RatTraits::sort(), 0);
    uwa.unify(a(x), 2, b + 3, 0);
  }
}

TEST_FUN(bug06) {
  for (auto mode : {
      Options::UnificationWithAbstraction::ALASCA_MAIN_FLOOR
      }) {
    auto uwa = AbstractingUnifier::empty(AbstractionOracle(mode));
    NUMBER_SUGAR(Rat)
    DECL_DEFAULT_VARS
    DECL_DEFAULT_SORT_VARS
    DECL_POLY_CONST(a, 1, alpha)
    DECL_CONST(b, Rat)

    uwa.unify(a(x), 2, b + 3, 0);
  }
}

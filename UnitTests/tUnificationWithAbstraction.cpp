/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#include "Forwards.hpp"
#include "Indexing/SubstitutionTree.hpp"
#include "Lib/Environment.hpp"

#include "Shell/Options.hpp"
#include "Test/TestUtils.hpp"

#include "Kernel/Unit.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/OperatorType.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/MismatchHandler.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/LiteralSubstitutionTree.hpp"
#include "Indexing/LiteralIndex.hpp"
#include "Indexing/TermSubstitutionTree.hpp"
#include "Indexing/TermIndex.hpp"

#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"

// TODO make this test use assertions, instead of printing output

using namespace Kernel;
using namespace Indexing;
#define TODO ASSERTION_VIOLATION_REP("TODO")

Clause* unit(Literal* lit)
{
  return clause({ lit });
}

static const auto tld = [](auto t) { return DefaultTermLeafData(t, nullptr, nullptr); };


unique_ptr<TermSubstitutionTree<>> getTermIndexHOL()
{ 
  return std::make_unique<TermSubstitutionTree<>>(Shell::Options::UnificationWithAbstraction::FUNC_EXT);
}

unique_ptr<TermSubstitutionTree<>> getTermIndex(Shell::Options::UnificationWithAbstraction uwa)
{ return std::make_unique<TermSubstitutionTree<>>(uwa); }

auto getLiteralIndex(Shell::Options::UnificationWithAbstraction uwa)
{ return std::make_unique<LiteralSubstitutionTree<>>(uwa); }

template<class TermOrLit>
struct UnificationResultSpec {
  TermOrLit querySigma;
  TermOrLit resultSigma;
  Stack<Literal*> constraints;

  friend bool operator==(UnificationResultSpec const& l, UnificationResultSpec const& r)
  {
    return Test::TestUtils::eqModAC(l.querySigma, r.querySigma)
       &&  Test::TestUtils::eqModAC(l.resultSigma, r.resultSigma)
       &&  Test::TestUtils::permEq(l.constraints, r.constraints,
             [](auto& l, auto& r) { return Test::TestUtils::eqModAC(l,r); });
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

void checkLiteralMatches(LiteralSubstitutionTree<>& index, Literal* lit, Stack<LiteralUnificationResultSpec> expected)
{
  Stack<LiteralUnificationResultSpec> is;
  for (auto qr : iterTraits(index.getUwa(lit, /* complementary */ false)) ) {
    // qr.substitution->numberOfConstraints();

    is.push(LiteralUnificationResultSpec {
        .querySigma = qr.unifier->subs().apply(lit, /* result */ QUERY_BANK),
        .resultSigma = qr.unifier->subs().apply(qr.literal, /* result */ RESULT_BANK),
        .constraints = *qr.unifier->constr().literals(qr.unifier->subs()),
    });
  }
  if (Test::TestUtils::permEq(is, expected, [](auto& l, auto& r) { return l == r; })) {
    cout << "[  OK  ] " << *lit << endl;
  } else {
    cout << "[ FAIL ] " << *lit << endl;
    cout << "tree: " << multiline(index, 1) << endl;
    cout << "query: " << *lit << endl;

    cout << "is:" << endl;
    for (auto& x : is)
      cout << "         " << x << endl;

    cout << "expected:" << endl;
    for (auto& x : expected)
      cout << "         " << x << endl;

    exit(-1);
  }
  // cout << endl;
}

template<class F>
void checkTermMatchesWithUnifFun(TermSubstitutionTree<>& index, TermList term, Stack<TermUnificationResultSpec> expected, F unifFun)
{
  CALL("checkTermMatchesWithUnifFun(TermSubstitutionTree<>& index, TermList term, Stack<TermUnificationResultSpec> expected, F unifFun)")
  Stack<TermUnificationResultSpec> is;
  for (auto qr : iterTraits(unifFun(index, term))) {
    is.push(TermUnificationResultSpec {
        .querySigma  = qr.unifier->subs().apply(term, /* result */ QUERY_BANK),
        .resultSigma = qr.unifier->subs().apply(qr.term, /* result */ RESULT_BANK),
        .constraints = *qr.unifier->constr().literals(qr.unifier->subs()),
    });
  }
  if (Test::TestUtils::permEq(is, expected, [](auto& l, auto& r) { return l == r; })) {
    cout << "[  OK  ] " << term << endl;
  } else {
    cout << "[ FAIL ] " << term << endl;
    cout << "tree: " << multiline(index, 1) << endl;
    cout << "query: " << term << endl;

    cout << "is:" << endl;
    for (auto& x : is)
      cout << "         " << x << endl;

    cout << "expected:" << endl;
    for (auto& x : expected)
      cout << "         " << x << endl;

    exit(-1);
  }
  // cout << endl;

}

void checkTermMatches(TermSubstitutionTree<>& index, TermList term, Stack<TermUnificationResultSpec> expected)
{
  ASS(term.isTerm())
  return checkTermMatchesWithUnifFun(index, term, expected, 
      [&](auto& idx, auto t) { return idx.getUwa(term.term()); });
}

void checkTermMatches(TermSubstitutionTree<>& index, TypedTermList term, Stack<TermUnificationResultSpec> expected)
{
  return checkTermMatchesWithUnifFun(index, term, expected, 
      [&](auto& idx, auto t) { return idx.getUwa(term); });
}

struct IndexTest {
  unique_ptr<TermSubstitutionTree<>> index;
  Stack<TermList> insert;
  TermSugar query;
  Stack<TermUnificationResultSpec> expected;

  void run() {
    CALL("IndexTest::run")

    DECL_PRED(dummy, {})
    for (auto x : this->insert) {
      index->insert(DefaultTermLeafData(x, dummy(), unit(dummy())));
    }

    checkTermMatches(*this->index, TypedTermList(this->query, this->query.sort()),this->expected);

  }
};


#define RAT_SUGAR                                                                                   \
   __ALLOW_UNUSED(                                                                                  \
      DECL_DEFAULT_VARS                                                                             \
      NUMBER_SUGAR(Rat)                                                                             \
      DECL_SORT(s)                                                                                  \
      DECL_FUNC(r2s, {Rat}, s)                                                                      \
      DECL_FUNC(s2r, {s}, Rat)                                                                      \
      DECL_PRED(p, {Rat})                                                                           \
      DECL_FUNC(f, {Rat}, Rat)                                                                      \
      DECL_FUNC(g, {Rat}, Rat)                                                                      \
      DECL_FUNC(f2, {Rat, Rat}, Rat)                                                                \
      DECL_FUNC(fa, {Rat, Rat}, Rat)                                                                \
      DECL_FUNC(g2, {Rat, Rat}, Rat)                                                                \
      DECL_CONST(a, Rat)                                                                            \
      DECL_CONST(b, Rat)                                                                            \
      DECL_CONST(c, Rat)                                                                            \
    )                                                                                               \
 

#define RUN_TEST(name, sugar, ...)                                                                  \
  TEST_FUN(name) {                                                                                  \
       __ALLOW_UNUSED(sugar)                                                                        \
       __VA_ARGS__.run();                                                                           \
  }                                                                                                 \

RUN_TEST(term_indexing_one_side_interp_01,
    RAT_SUGAR,
    IndexTest {
      .index = getTermIndex(Options::UnificationWithAbstraction::ONE_INTERP),
      .insert = {
        f(1 + num(1)),
        f(1 + a),
      },
      .query = f(x),
      .expected = { 

          TermUnificationResultSpec 
          { .querySigma  = f(1 + a),
            .resultSigma = f(1 + a),
            .constraints = Stack<Literal*>() }, 

          TermUnificationResultSpec 
          { .querySigma  = f(1 + num(1)),
            .resultSigma = f(1 + num(1)),
            .constraints = Stack<Literal*>() }, 

      },
    })


RUN_TEST(term_indexing_one_side_interp_02, 
    RAT_SUGAR,
    IndexTest {
      .index = getTermIndex(Options::UnificationWithAbstraction::ONE_INTERP),
      .insert = {
        f(1 + num(1)),
        f(1 + a),
      },
      .query = g(x),
      .expected = Stack<TermUnificationResultSpec>(),
    })
 
RUN_TEST(term_indexing_one_side_interp_03, 
    RAT_SUGAR,
    IndexTest {
      .index = getTermIndex(Options::UnificationWithAbstraction::ONE_INTERP),
      .insert = {
        1 + num(1),
        1 + a,
      },
      .query = x.sort(Rat),
      .expected = { 

        TermUnificationResultSpec 
        { .querySigma  = 1 + a,
          .resultSigma = 1 + a,
          .constraints = Stack<Literal*>() }, 

        TermUnificationResultSpec 
        { .querySigma  = 1 + num(1),
          .resultSigma = 1 + num(1),
          .constraints = Stack<Literal*>() }, 

      }
    })


RUN_TEST(term_indexing_one_side_interp_04, 
    RAT_SUGAR,
    IndexTest {
      .index = getTermIndex(Options::UnificationWithAbstraction::ONE_INTERP),
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



RUN_TEST(term_indexing_one_side_interp_04_b, 
    RAT_SUGAR,
    IndexTest {
      .index = getTermIndex(Options::UnificationWithAbstraction::ONE_INTERP),
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


RUN_TEST(term_indexing_one_side_interp_04_c, 
    RAT_SUGAR,
    IndexTest {
      .index = getTermIndex(Options::UnificationWithAbstraction::ONE_INTERP),
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

RUN_TEST(term_indexing_one_side_interp_04_d, 
    RAT_SUGAR,
    IndexTest {
      .index = getTermIndex(Options::UnificationWithAbstraction::ONE_INTERP),
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

RUN_TEST(term_indexing_one_side_interp_05, 
    RAT_SUGAR,
    IndexTest {
      .index = getTermIndex(Options::UnificationWithAbstraction::ONE_INTERP),
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


RUN_TEST(term_indexing_one_side_interp_06, 
    RAT_SUGAR,
    IndexTest {
      .index = getTermIndex(Options::UnificationWithAbstraction::ONE_INTERP),
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


RUN_TEST(term_indexing_one_side_interp_07, 
    RAT_SUGAR,
    IndexTest {
      .index = getTermIndex(Options::UnificationWithAbstraction::ONE_INTERP),
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

RUN_TEST(term_indexing_one_side_interp_08, 
    RAT_SUGAR,
    IndexTest {
      .index = getTermIndex(Options::UnificationWithAbstraction::ONE_INTERP),
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

TEST_FUN(term_indexing_poly_01)
{
  auto index = getTermIndex(Options::UnificationWithAbstraction::ONE_INTERP);

  DECL_DEFAULT_VARS
  DECL_DEFAULT_SORT_VARS  
  NUMBER_SUGAR(Rat)
  DECL_CONST(a, Rat) 
  DECL_POLY_CONST(h, 1, alpha)
  DECL_SORT(A)

  index->insert(tld(1 + a ));
  index->insert(tld(h(Rat)));

  checkTermMatches(*index, h(alpha), Stack<TermUnificationResultSpec>{

        TermUnificationResultSpec 
        { .querySigma  = h(Rat),
          .resultSigma = h(Rat),
          .constraints = Stack<Literal*>{  } }, 

        TermUnificationResultSpec 
        { .querySigma  = h(Rat),
          .resultSigma = 1 + a,
          .constraints = { 1 + a != h(Rat), } }, 

      });

  checkTermMatches(*index, h(A), Stack<TermUnificationResultSpec>{ });
}


#define POLY_RAT_SUGAR                                                                              \
  DECL_DEFAULT_VARS                                                                                 \
  DECL_DEFAULT_SORT_VARS                                                                            \
  NUMBER_SUGAR(Rat)                                                                                 \
  DECL_POLY_CONST(b, 1, alpha)                                                                      \
  DECL_POLY_CONST(a, 1, alpha)                                                                      \
  DECL_POLY_FUNC(f, 1, {alpha}, alpha)                                                              \
  DECL_SORT(A)                                                                                      \
  DECL_CONST(someA, A)                                                                              \


#define HOL_SUGAR(...)                                                                              \
  DECL_DEFAULT_VARS                                                                                 \
  DECL_DEFAULT_SORT_VARS                                                                            \
  NUMBER_SUGAR(Rat)                                                                                 \
  DECL_SORT(srt)                                                                                    \
  __VA_ARGS__

 


RUN_TEST(hol_0101,
    HOL_SUGAR(
      DECL_FUNC(f3, {srt, srt, srt}, srt)
      DECL_CONST(f1, arrow(srt, srt))
      DECL_CONST(f2, arrow(srt, srt))
      DECL_CONST(h, arrow(arrow(srt, srt), srt))
    ),
    IndexTest {
      .index = getTermIndexHOL(),
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


RUN_TEST(hol_0102,
    HOL_SUGAR(
      DECL_FUNC(f3, {srt, srt, srt}, srt)
      DECL_CONST(f1, arrow(srt, srt))
      DECL_CONST(f2, arrow(srt, srt))
      DECL_CONST(h, arrow(arrow(srt, srt), srt))
    ),
    IndexTest {
      .index = getTermIndexHOL(),
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


RUN_TEST(hol_02,
    HOL_SUGAR(
      DECL_FUNC(f3, {srt, srt, srt}, srt)
      DECL_CONST(f1, arrow(srt, srt))
      DECL_CONST(f2, arrow(srt, srt))
      DECL_CONST(a, srt)
      DECL_CONST(h, arrow(arrow(srt, srt), srt))
      ),
    IndexTest {
      .index = getTermIndexHOL(),
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


RUN_TEST(hol_03,
    HOL_SUGAR(
      DECL_FUNC(f3, {srt, srt, srt}, srt)
      DECL_CONST(f1, arrow(srt, srt))
      DECL_CONST(f2, arrow(srt, srt))
      DECL_CONST(h1, arrow(arrow(srt, srt), srt))
      DECL_CONST(h2, arrow(arrow(srt, srt), srt))
    ),
    IndexTest {
      .index = getTermIndexHOL(),
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

#define RUN_TEST_hol_04(idx, ...)                                                                   \
  RUN_TEST(hol_04_ ## idx,                                                                          \
    HOL_SUGAR(                                                                                      \
      DECL_FUNC(f3, {srt, srt, srt}, srt)                                                           \
      DECL_POLY_CONST(c1, 1, alpha)                                                                 \
      DECL_POLY_CONST(c2, 1, alpha)                                                                 \
      DECL_POLY_CONST(h, 2, arrow(alpha, beta))                                                     \
    ),                                                                                              \
    IndexTest {                                                                                     \
      .index = getTermIndexHOL(),                                                                   \
      .insert = {                                                                                   \
               ap(h(arrow(srt, srt), srt), c1(arrow(srt, srt))),                                    \
               ap(h(srt            , srt), c1(srt)),                                                \
      },                                                                                            \
      __VA_ARGS__                                                                                   \
    })


RUN_TEST_hol_04(01,
      .query = ap(h(arrow(srt,srt), srt), c1(arrow(srt, srt))),
      .expected =  {
        TermUnificationResultSpec 
        { .querySigma  = ap(h(arrow(srt,srt), srt), c1(arrow(srt, srt))),
          .resultSigma = ap(h(arrow(srt,srt), srt), c1(arrow(srt, srt))),
          .constraints = Stack<Literal*>{} }, 
      }
    )

RUN_TEST_hol_04(02,
      .query = ap(h(arrow(srt,srt), srt), c2(arrow(srt, srt))),
      .expected =  {
        TermUnificationResultSpec 
        { .querySigma  = ap(h(arrow(srt,srt), srt), c2(arrow(srt, srt))),
          .resultSigma = ap(h(arrow(srt,srt), srt), c1(arrow(srt, srt))),
          .constraints = Stack<Literal*>{ c1(arrow(srt,srt)) != c2(arrow(srt,srt)) } }, 
      }
    )


#define RUN_TEST_hol_05(idx, ...)                                                                   \
  RUN_TEST(hol_05_ ## idx,                                                                          \
    HOL_SUGAR(                                                                                      \
      DECL_FUNC(f3, {srt, srt, srt}, srt)                                                           \
      DECL_POLY_CONST(c1, 1, alpha)                                                                 \
      DECL_POLY_CONST(c2, 1, alpha)                                                                 \
      DECL_POLY_CONST(h, 2, arrow(alpha, beta))                                                     \
    ),                                                                                              \
    IndexTest {                                                                                     \
      .index = getTermIndexHOL(),                                                                   \
      .insert = {                                                                                   \
               ap(h(arrow(srt, srt), srt), c1(arrow(srt, srt))),                                    \
               ap(h(srt            , srt), c2(srt)),                                                \
      },                                                                                            \
      __VA_ARGS__                                                                                   \
    })


RUN_TEST_hol_05(01,
      .query = ap(h(arrow(srt,srt), srt), c1(arrow(srt, srt))),
      .expected =  {
        TermUnificationResultSpec 
        { .querySigma  = ap(h(arrow(srt,srt), srt), c1(arrow(srt, srt))),
          .resultSigma = ap(h(arrow(srt,srt), srt), c1(arrow(srt, srt))),
          .constraints = Stack<Literal*>{} }, 
      }
    )

RUN_TEST_hol_05(02,
      .query = ap(h(arrow(srt,srt), srt), c2(arrow(srt, srt))),
      .expected =  {
        TermUnificationResultSpec 
        { .querySigma  = ap(h(arrow(srt,srt), srt), c2(arrow(srt, srt))),
          .resultSigma = ap(h(arrow(srt,srt), srt), c1(arrow(srt, srt))),
          .constraints = Stack<Literal*>{ c1(arrow(srt,srt)) != c2(arrow(srt,srt)) } }, 
      }
    )

RUN_TEST(term_indexing_poly_uwa_01,
    POLY_RAT_SUGAR,
    IndexTest {
      .index = getTermIndex(Options::UnificationWithAbstraction::ONE_INTERP),
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
        { .querySigma  = f(Rat, a(Rat) + y),
          .resultSigma = f(Rat, b(Rat)),
          .constraints = { b(Rat) != a(Rat) + y } }, 

      }
    })


TEST_FUN(term_indexing_interp_only)
{
  auto index = getTermIndex(Options::UnificationWithAbstraction::INTERP_ONLY);

  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Rat)

  DECL_CONST(a, Rat) 
  DECL_CONST(b, Rat) 

  index->insert(tld(num(1) + num(1)));
  index->insert(tld(1 + a          ));

  checkTermMatches(*index, b + 2, {

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

  checkTermMatches(*index, b + 2 , {

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
  auto index = getLiteralIndex(Options::UnificationWithAbstraction::ONE_INTERP);

  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Rat)
  DECL_PRED(p, {Rat})

  DECL_CONST(a, Rat) 
  DECL_CONST(b, Rat) 

  index->insert(p(num(1) + num(1)), nullptr);
  index->insert(p(1 + a          ), nullptr);

  checkLiteralMatches(*index,p(b + 2),{

      LiteralUnificationResultSpec {
        .querySigma = p(b + 2),
        .resultSigma = p(num(1) + 1),
        .constraints = { b + 2 != num(1) + 1 }, },

      LiteralUnificationResultSpec {
        .querySigma = p(b + 2),
        .resultSigma = p(a + 1),
        .constraints = { b + 2 != a + 1 }, },

      });

  index->insert(p(b + 2),unit(p(b + 2)));
  index->insert(p(2 + b),unit(p(2 + b)));

  checkLiteralMatches(*index,p(b + 2),{

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
  auto index = getTermIndexHOL();

  index->insert(tld(ap(f,a)));

  checkTermMatches(*index, ap(f,b), Stack<TermUnificationResultSpec>{

        TermUnificationResultSpec 
        { .querySigma  = ap(f,b),
          .resultSigma = ap(f,a),
          .constraints = { a != b, } }, 

      });

  index->insert(tld(ap(g,c)));
  index->insert(tld(g));

  checkTermMatches(*index, TypedTermList(x, arrow(srt, srt)), Stack<TermUnificationResultSpec>{

        TermUnificationResultSpec 
        { .querySigma  = ap(g,c),
          .resultSigma = ap(g,c),
          .constraints = Stack<Literal*>{} }, 

      });

  checkTermMatches(*index, ap(f,b), Stack<TermUnificationResultSpec>{

        TermUnificationResultSpec 
        { .querySigma  = ap(f,b),
          .resultSigma = ap(f,a),
          .constraints = { a != b, } }, 

      });



  // index->insert(h(alpha), 0, 0);
  //
  // checkTermMatches(*index,x,arrow(srt, srt), Stack<TermUnificationResultSpec>{
  //
  //       TermUnificationResultSpec 
  //       { .querySigma  = ap(f,a),
  //         .resultSigma = ap(f,a),
  //         .constraints = Stack<Literal*>{} }, 
  //
  //     });


  // TODO
  // reportTermMatches(index,h(beta),beta);
  // reportTermMatches(index,h(srt),srt);
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

  // TODO
  // reportTermMatches(index,ap(ap(f,b),a),srt);
}

static const int NORM_QUERY_BANK=2;
// static const int NORM_RESULT_BANK=3;

Option<TermUnificationResultSpec> runRobUnify(TermList a, TermList b, Options::UnificationWithAbstraction opt) {
  MismatchHandler h(opt);
  AbstractingUnifier au(h);
  bool result = au.unify(a, 0, b, 0);
  if (result) {

    return some(TermUnificationResultSpec { 
     .querySigma  = au.subs().apply(a, 0), 
     .resultSigma = au.subs().apply(b, 0), 
     .constraints = *au.constr().literals(au.subs()),
    });

  } else {
    return none<TermUnificationResultSpec>();
  }


}

void checkRobUnify(TermList a, TermList b, Options::UnificationWithAbstraction opt, TermUnificationResultSpec exp)
{
  auto is = runRobUnify(a,b,opt);
  if (is.isSome() && is.unwrap() == exp) {
    cout << "[  OK  ] " << a << " unify " << b << endl;
  } else {
    cout << "[ FAIL ] " << a << " unify " << b << endl;
    cout << "is:       " << is << endl;
    cout << "expected: " << exp << endl;
    exit(-1);
  }
}


void checkRobUnifyFail(TermList a, TermList b, Options::UnificationWithAbstraction opt)
{
  auto is = runRobUnify(a,b,opt);
  if(is.isNone()) {
      cout << "[  OK  ] " << a << " unify " << b << endl;
  } else {
    cout << "[ FAIL ] " << a << " unify " << b << endl;
    cout << "is:       " << is << endl;
    cout << "expected: nothing" << endl;
    exit(-1);
  }
}

#define ROB_UNIFY_TEST(name, opt, lhs, rhs, ...)                                                    \
  TEST_FUN(name)                                                                                    \
  {                                                                                                 \
    RAT_SUGAR                                                                                       \
    checkRobUnify(lhs, rhs, opt, __VA_ARGS__ );                                                     \
  }                                                                                                 \

#define ROB_UNIFY_TEST_FAIL(name, opt, lhs, rhs)                                                    \
  TEST_FUN(name)                                                                                    \
  {                                                                                                 \
    RAT_SUGAR                                                                                       \
    checkRobUnifyFail(lhs, rhs, opt);                                                               \
  }                                                                                                 \

ROB_UNIFY_TEST(rob_unif_test_01,
    Options::UnificationWithAbstraction::ONE_INTERP,
    f(b + 2), 
    f(x + 2),
    TermUnificationResultSpec { 
      .querySigma = f(b + 2),
      .resultSigma = f(x + 2),
      .constraints = { x + 2 != b + 2 },
    })

ROB_UNIFY_TEST(rob_unif_test_02,
    Options::UnificationWithAbstraction::ONE_INTERP,
    f(b + 2), 
    f(x + 2),
    TermUnificationResultSpec { 
      .querySigma = f(b + 2),
      .resultSigma = f(x + 2),
      .constraints = { x + 2 != b + 2 },
    })

ROB_UNIFY_TEST(rob_unif_test_03,
    Options::UnificationWithAbstraction::ONE_INTERP,
    f(x + 2), 
    f(a),
    TermUnificationResultSpec { 
      .querySigma = f(x + 2),
      .resultSigma = f(a),
      .constraints = { x + 2 != a },
    })

ROB_UNIFY_TEST_FAIL(rob_unif_test_04,
    Options::UnificationWithAbstraction::ONE_INTERP,
    f(a), g(1 + a))


ROB_UNIFY_TEST(rob_unif_test_05,
    Options::UnificationWithAbstraction::ONE_INTERP,
    f(a + b), 
    f(x + y),
    TermUnificationResultSpec { 
      .querySigma = f(a + b),
      .resultSigma = f(x + y),
      .constraints = { x + y != a + b },
    })

ROB_UNIFY_TEST(rob_unif_test_06,
    Options::UnificationWithAbstraction::ONE_INTERP,
    f2(x, x + 1), 
    f2(a, a),
    TermUnificationResultSpec { 
      .querySigma = f2(a, a + 1),
      .resultSigma = f2(a, a),
      .constraints = { a != a + 1 },
    })

// ROB_UNIFY_TEST(over_approx_test_1_bad,
//     Options::UnificationWithAbstraction::AC1,
//     f2(x + b, x),
//     f2(a    , a),
//     TermUnificationResultSpec { 
//       .querySigma  = f2(a + b, a),
//       .resultSigma = f2(a    , a),
//       .constraints = { a != a + b },
//     })
//
// ROB_UNIFY_TEST_FAIL(over_approx_test_1_good,
//     Options::UnificationWithAbstraction::AC1,
//     f2(x, x + b),
//     f2(a, a    ))

ROB_UNIFY_TEST(over_approx_test_2_bad_AC1,
    Options::UnificationWithAbstraction::AC1,
    f2(x, a + x),
    f2(c, b + a),
    TermUnificationResultSpec { 
      .querySigma  = f2(c, a + c),
      .resultSigma = f2(c, b + a),
      .constraints = { c != b },
    })

ROB_UNIFY_TEST_FAIL(over_approx_test_2_good_AC1,
    Options::UnificationWithAbstraction::AC1,
    f2(a + x, x),
    f2(b + a, c))

ROB_UNIFY_TEST(bottom_constraint_test_1_bad_AC1,
    Options::UnificationWithAbstraction::AC1,
    f2(f2(y, x), a + y + x),
    f2(f2(b, c), c + b + a),
    TermUnificationResultSpec { 
      .querySigma  = f2(f2(b,c), a + b + c),
      .resultSigma = f2(f2(b,c), c + b + a),
      .constraints = Stack<Literal*>{ b + c != c + b },
    })

ROB_UNIFY_TEST(bottom_constraint_test_1_good_AC1,
    Options::UnificationWithAbstraction::AC1,
    f2(a + x + y, f2(x, y)),
    f2(c + b + a, f2(b, c)),
    // f2(a + x, x),
    // f2(b + a, b),
    TermUnificationResultSpec { 
      .querySigma  = f2(a + b + c, f2(b,c)),
      .resultSigma = f2(c + b + a, f2(b,c)),
      .constraints = Stack<Literal*>{},
    })


ROB_UNIFY_TEST(ac_test_01_AC1,
    Options::UnificationWithAbstraction::AC1,
    f2(b, a + b + c),
    f2(b, x + y + c),
    TermUnificationResultSpec { 
      .querySigma  = f2(b, a + b + c),
      .resultSigma = f2(b, x + y + c),
      .constraints = { a + b != x + y },
    })

ROB_UNIFY_TEST(ac_test_02_AC1_bad,
    Options::UnificationWithAbstraction::AC1,
    f2(a + b + c, c),
    f2(x + y + z, z),
    TermUnificationResultSpec { 
      .querySigma  = f2(a + b + c, c),
      .resultSigma = f2(x + y + c, c),
      .constraints = { a + b != x + y },
    })

ROB_UNIFY_TEST(ac_test_02_AC1_good,
    Options::UnificationWithAbstraction::AC1,
    f2(c, a + b + c),
    f2(z, x + y + z),
    TermUnificationResultSpec { 
      .querySigma  = f2(c, a + b + c),
      .resultSigma = f2(c, x + y + c),
      .constraints = { a + b + c != x + y + c },
    })

ROB_UNIFY_TEST(ac2_test_01,
    Options::UnificationWithAbstraction::AC2,
    f2(x, a + b + c),
    f2(x, x + b + a),
    TermUnificationResultSpec { 
      .querySigma  = f2(c, a + b + c),
      .resultSigma = f2(c, c + b + a),
      .constraints = Stack<Literal*>{},
    })

ROB_UNIFY_TEST(ac2_test_02,
    Options::UnificationWithAbstraction::AC2,
    f2(a + b + c, f2(x,b)),
    f2(x + y + a, f2(x,y)),
    TermUnificationResultSpec { 
      .querySigma  = f2(a + b + c, f2(c,b)),
      .resultSigma = f2(c + b + a, f2(c,b)),
      .constraints = Stack<Literal*>{},
    })

ROB_UNIFY_TEST(ac2_test_02_bad,
    Options::UnificationWithAbstraction::AC2,
    f2(f2(x,b), a + b + c),
    f2(f2(x,y), x + y + a),
    TermUnificationResultSpec { 
      .querySigma  = f2(f2(x,b), a + b + c),
      .resultSigma = f2(f2(x,b), x + b + a),
      .constraints = Stack<Literal*>{ b + c != x + b },
    })



ROB_UNIFY_TEST(alasca3_test_01,
    Options::UnificationWithAbstraction::ALASCA3,
    f2(x, a + b + c),
    f2(x, x + b + a),
    TermUnificationResultSpec { 
      .querySigma  = f2(c, a + b + c),
      .resultSigma = f2(c, c + b + a),
      .constraints = Stack<Literal*>{},
    })

ROB_UNIFY_TEST(alasca3_test_02,
    Options::UnificationWithAbstraction::ALASCA3,
    f2(a + b + c, f2(x,b)),
    f2(x + y + a, f2(x,y)),
    TermUnificationResultSpec { 
      .querySigma  = f2(a + b + c, f2(c,b)),
      .resultSigma = f2(c + b + a, f2(c,b)),
      .constraints = Stack<Literal*>{},
    })

ROB_UNIFY_TEST(alasca3_test_02_bad,
    Options::UnificationWithAbstraction::ALASCA3,
    f2(f2(x,b), a + b + c),
    f2(f2(x,y), x + y + a),
    TermUnificationResultSpec { 
      .querySigma  = f2(f2(x,b), a + b + c),
      .resultSigma = f2(f2(x,b), x + b + a),
      .constraints = Stack<Literal*>{ b + x != c + b },
    })


ROB_UNIFY_TEST(alasca3_test_03,
    Options::UnificationWithAbstraction::ALASCA3,
    f2(x, a + b + c),
    f2(x, x + b + a),
    TermUnificationResultSpec { 
      .querySigma  = f2(c, a + b + c),
      .resultSigma = f2(c, c + b + a),
      .constraints = Stack<Literal*>{ },
    })


ROB_UNIFY_TEST(alasca3_test_04,
    Options::UnificationWithAbstraction::ALASCA3,
    f2(x, 2 * a + b + c),
    f2(x, x     + b + a),
    TermUnificationResultSpec { 
      .querySigma  = f2(a + c,  2 * a  + b + c),
      .resultSigma = f2(a + c, (a + c) + b + a),
      .constraints = Stack<Literal*>{ },
    })

ROB_UNIFY_TEST(alasca3_test_05,
    Options::UnificationWithAbstraction::ALASCA3,
    f2(x, 2 * a + b + c),
    f2(x, x     + b + y),
    TermUnificationResultSpec { 
      .querySigma  = f2(x,  2 * a  + b + c),
      .resultSigma = f2(x,  x      + b + y),
      .constraints = Stack<Literal*>{ x + y != 2 * a + c },
    })


ROB_UNIFY_TEST(alasca3_test_06,
    Options::UnificationWithAbstraction::ALASCA3,
    f2(x, 2 * a +             b + c),
    f2(x, x     + frac(1,2) * b + y),
    TermUnificationResultSpec { 
      .querySigma  = f2(x, 2 * a +             b + c),
      .resultSigma = f2(x, x     + frac(1,2) * b + y),
      .constraints = Stack<Literal*>{ x + y != 2 * a + frac(1,2) * b + c },
    })


ROB_UNIFY_TEST(alasca3_test_07,
    Options::UnificationWithAbstraction::ALASCA3,
    f2(x, f(x) + y),
    f2(x, f(y) + y),
    TermUnificationResultSpec { 
      .querySigma  = f2(x, f(x) + x),
      .resultSigma = f2(x, f(x) + x),
      .constraints = Stack<Literal*>{},
    })


ROB_UNIFY_TEST_FAIL(alasca3_test_08,
    Options::UnificationWithAbstraction::ALASCA3,
    f2(x, a + b),
    f2(x, c + b))

ROB_UNIFY_TEST_FAIL(alasca3_test_09,
    Options::UnificationWithAbstraction::ALASCA3,
    f2(x, f(a) + b),
    f2(x, f(y) + g(y)))


ROB_UNIFY_TEST(alasca3_test_10,
    Options::UnificationWithAbstraction::ALASCA3,
    f2(x, a + b + x),
    f2(x, c + b),
    TermUnificationResultSpec { 
      .querySigma  = f2(-a + c, a + b + (-a + c)),
      .resultSigma = f2(-a + c, c + b),
      .constraints = Stack<Literal*>{},
    })

ROB_UNIFY_TEST_FAIL(alasca3_test_11,
    Options::UnificationWithAbstraction::ALASCA3,
    f2(x, f(a) +  2 * g(a)),
    f2(x, frac(1,2) * f(a) + g(x) + g(y)))

ROB_UNIFY_TEST_FAIL(alasca3_test_12,
    Options::UnificationWithAbstraction::ALASCA3,
    f2(x, f(x) + f(b) + f(z)),
    f2(x, f(a) - f(y)))

ROB_UNIFY_TEST_FAIL(alasca3_test_13,
    Options::UnificationWithAbstraction::ALASCA3,
    f2(x, f(x)),
    f2(x, f(a) - f(y)))

ROB_UNIFY_TEST(alasca3_test_14,
    Options::UnificationWithAbstraction::ALASCA3,
    f2(x, 0),
    f2(x, f(a) - f(y)),
    TermUnificationResultSpec { 
      .querySigma  = f2(x, 0),
      .resultSigma = f2(x, f(a) - f(a)),
      .constraints = Stack<Literal*>{},
    })

ROB_UNIFY_TEST(constr_var_01,
    Options::UnificationWithAbstraction::ALASCA3,
    s2r(x),
    s2r(r2s(s2r(x) + y)),
    TermUnificationResultSpec { 
      .querySigma  = s2r(x),
      .resultSigma = s2r(r2s(s2r(x) + y)),
      .constraints = Stack<Literal*>{x != r2s(s2r(x) + y)},
    })



ROB_UNIFY_TEST(constr_var_02,
    Options::UnificationWithAbstraction::ALASCA3,
    x,
    f(x + f(y)),
    TermUnificationResultSpec { 
      .querySigma  = x,
      .resultSigma = f(x + f(y)),
      .constraints = { x != f(x + f(y)) },
    })


ROB_UNIFY_TEST(constr_var_03,
    Options::UnificationWithAbstraction::ALASCA3,
    x,
    f(y + f(x)),
    TermUnificationResultSpec { 
      .querySigma  = x,
      .resultSigma = f(y + f(x)),
      .constraints = { x != f(y + f(x)) },
    })

ROB_UNIFY_TEST_FAIL(constr_var_04,
    Options::UnificationWithAbstraction::ALASCA3,
    x,
    f(f(x)))

ROB_UNIFY_TEST_FAIL(constr_var_05,
    Options::UnificationWithAbstraction::ALASCA3,
    x,
    f2(x, y + f(x))
  )

ROB_UNIFY_TEST_FAIL(constr_var_06,
    Options::UnificationWithAbstraction::ALASCA3,
    x,
    f2(y + f(x), x)
  )

ROB_UNIFY_TEST_FAIL(constr_var_07,
    Options::UnificationWithAbstraction::ALASCA3,
    x,
    f2(f(x), x)
  )

ROB_UNIFY_TEST(constr_var_08,
    Options::UnificationWithAbstraction::ALASCA3,
    x,
    f2(y + f(x), y + f(x)),
    TermUnificationResultSpec { 
      .querySigma  = x,
      .resultSigma = f2(y + f(x), y + f(x)),
      .constraints = { x != f2(y + f(x), y + f(x)) },
    })

ROB_UNIFY_TEST(constr_var_09,
    Options::UnificationWithAbstraction::ALASCA3,
    x,
    f2(f(y) + x, y + f(x)),
    TermUnificationResultSpec { 
      .querySigma  = x,
      .resultSigma = f2(f(y) + x, y + f(x)),
      .constraints = { x != f2(f(y) + x, y + f(x)) },
    })


ROB_UNIFY_TEST(constr_var_10,
    Options::UnificationWithAbstraction::ALASCA3,
    f2(x, y),
    f2(y * x, 0),
    TermUnificationResultSpec { 
      .querySigma  = f2(x    , 0),
      .resultSigma = f2(0 * x, 0),
      .constraints = { x != 0 * x },
    })



ROB_UNIFY_TEST(constr_var_11,
    Options::UnificationWithAbstraction::ALASCA3,
    f2(x, y),
    f2(x * y, 0),
    TermUnificationResultSpec { 
      .querySigma  = f2(x    , 0),
      .resultSigma = f2(x * 0, 0),
      .constraints = { x != x * 0 },
    })

// TODO?
// ROB_UNIFY_TEST_FAIL(constr_var_12,
//     Options::UnificationWithAbstraction::ALASCA3,
//     f2(x, y),
//     f2(y * x, 5))
//
// ROB_UNIFY_TEST_FAIL(constr_var_13,
//     Options::UnificationWithAbstraction::ALASCA3,
//     f2(x, y),
//     f2(x * y, 5))
//
// ROB_UNIFY_TEST_FAIL(constr_var_14,
//     Options::UnificationWithAbstraction::ALASCA3,
//     x,
//     f(x) + g(x))



ROB_UNIFY_TEST(bug01,
    Options::UnificationWithAbstraction::ALASCA3,
    f2(x - y, f2(x, y)),
    f2(0    , f2(x, y)),
    TermUnificationResultSpec { 
      .querySigma  = f2(x - x, f2(x,x)),
      .resultSigma = f2(0    , f2(x,x)),
      .constraints = Stack<Literal*>{ },
    })


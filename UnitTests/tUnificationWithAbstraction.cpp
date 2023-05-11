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

#if VHOL
#include "Shell/LambdaConversion.hpp"
#endif

#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"

#include "z3++.h"
#include <ios>


using namespace Kernel;
using namespace Indexing;

#define TODO ASSERTION_VIOLATION_REP("TODO")

#if VHOL
TermList toDBs(TermList t){
  return LambdaConversion().convertLambda(t);
}
#endif

Clause* unit(Literal* lit)
{
  return clause({ lit });
}

unique_ptr<TermSubstitutionTree> getTermIndex()
{ 
  return std::make_unique<TermSubstitutionTree>(/* extra */ false);
}

auto getLiteralIndex()
{ return std::make_unique<LiteralSubstitutionTree>(); }

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

void checkLiteralMatches(LiteralSubstitutionTree& index, Literal* lit, Stack<LiteralUnificationResultSpec> expected)
{
  Stack<LiteralUnificationResultSpec> is;
  for (auto qr : iterTraits(index.getUwa(lit, /* complementary */ false)) ) {
    // qr.substitution->numberOfConstraints();

    is.push(LiteralUnificationResultSpec {
        .querySigma = qr.unifier->apply(lit, QUERY_BANK),
        .resultSigma = qr.unifier->apply(qr.literal, RESULT_BANK),
        .constraints = *qr.unifier->getConstraints(),
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
void checkTermMatchesWithUnifFun(TermSubstitutionTree& index, TermList term, Stack<TermUnificationResultSpec> expected, F unifFun)
{
  CALL("checkTermMatchesWithUnifFun(TermSubstitutionTree& index, TermList term, Stack<TermUnificationResultSpec> expected, F unifFun)")

  Stack<TermUnificationResultSpec> is;
  for (auto qr : iterTraits(unifFun(index, term))) {
    is.push(TermUnificationResultSpec {
        .querySigma  = qr.unifier->applyTo(term, QUERY_BANK) ,
        .resultSigma = qr.unifier->applyTo(qr.term, RESULT_BANK) ,
        .constraints = *qr.unifier->getConstraints(),
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

void checkTermMatches(TermSubstitutionTree& index, TypedTermList term, Stack<TermUnificationResultSpec> expected)
{
  checkTermMatchesWithUnifFun(index, term, expected,
      [&](auto& idx, auto t) { return idx.getUwa(term); });
}

#if VHOL
void checkHigherOrderTermMatches(TermSubstitutionTree& index, TypedTermList term, Stack<TermUnificationResultSpec> expected)
{
  checkTermMatchesWithUnifFun(index, term, expected,
      [&](auto& idx, auto t) { return idx.getHOLUnifiers(term); });
}
#endif

struct IndexTest {
  unique_ptr<TermSubstitutionTree> index;
  Stack<TypedTermList> insert;
  TermSugar query;
  Stack<TermUnificationResultSpec> expected;
  vstring uwa;
  vstring fixedPointIteration = "off";

  void run() {
    CALL("IndexTest::run")

    env.options->set("unification_with_abstraction", uwa);
    env.options->set("unification_with_abstraction_postpro", fixedPointIteration);
 
    DECL_PRED(dummy, Stack<SortSugar>())
    for (auto x : this->insert) {
      index->insert(x, dummy(), unit(dummy()));
    }

    checkTermMatches(*this->index, TypedTermList(this->query, this->query.sort()),this->expected);

  }
};


#define INT_SUGAR                                                                                   \
   __ALLOW_UNUSED(                                                                                  \
      DECL_DEFAULT_VARS                                                                             \
      DECL_VAR(x0, 0)                                                                               \
      DECL_VAR(x1, 1)                                                                               \
      DECL_VAR(x2, 2)                                                                               \
      DECL_VAR(x3, 3)                                                                               \
      NUMBER_SUGAR(Int)                                                                             \
      DECL_PRED(p, {Int})                                                                           \
      DECL_FUNC(f, {Int}, Int)                                                                      \
      DECL_FUNC(g, {Int}, Int)                                                                      \
      DECL_FUNC(f2, {Int, Int}, Int)                                                                \
      DECL_FUNC(g2, {Int, Int}, Int)                                                                \
      DECL_CONST(a, Int)                                                                            \
      DECL_CONST(b, Int)                                                                            \
      DECL_CONST(c, Int)                                                                            \
    )                                                                                               \
 

#define RUN_TEST(name, sugar, ...)                                                                  \
  TEST_FUN(name) {                                                                                  \
       __ALLOW_UNUSED(sugar)                                                                        \
       __VA_ARGS__.run();                                                                           \
  }                                                                                                 \

RUN_TEST(term_indexing_one_side_interp_01,
    INT_SUGAR,
    IndexTest {
      .index = getTermIndex(),
      .uwa = "one_side_interpreted",
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
    INT_SUGAR,
    IndexTest {
      .index = getTermIndex(),
      .uwa = "one_side_interpreted",
      .insert = {
        f(1 + num(1)),
        f(1 + a),
      },
      .query = g(x),
      .expected = Stack<TermUnificationResultSpec>(),
    })
 
RUN_TEST(term_indexing_one_side_interp_03, 
    INT_SUGAR,
    IndexTest {
      .index = getTermIndex(),
      .uwa = "one_side_interpreted",
      .insert = {
        1 + num(1),
        1 + a,
      },
      .query = x.sort(Int),
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
    INT_SUGAR,
    IndexTest {
      .index = getTermIndex(),
      .uwa = "one_side_interpreted",
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
    INT_SUGAR,
    IndexTest {
      .index = getTermIndex(),
      .uwa = "one_side_interpreted",
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
    INT_SUGAR,
    IndexTest {
      .index = getTermIndex(),
      .uwa = "one_side_interpreted",
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
    INT_SUGAR,
    IndexTest {
      .index = getTermIndex(),
      .uwa = "one_side_interpreted",
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
    INT_SUGAR,
    IndexTest {
      .index = getTermIndex(),
      .uwa = "one_side_interpreted",
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
    INT_SUGAR,
    IndexTest {
      .index = getTermIndex(),
      .uwa = "one_side_interpreted",
      .insert = {
        1 + num(1),
        1 + a,
        a,
      },
      .query = x.sort(Int),
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
    INT_SUGAR,
    IndexTest {
      .index = getTermIndex(),
      .uwa = "one_side_interpreted",
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
    INT_SUGAR,
    IndexTest {
      .index = getTermIndex(),
      .uwa = "one_side_interpreted",
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
  env.options->set("unification_with_abstraction", "one_side_interpreted");
  env.options->set("unification_with_abstraction_postpro", "off");

  auto index = getTermIndex();

  DECL_DEFAULT_VARS
  DECL_DEFAULT_SORT_VARS  
  NUMBER_SUGAR(Int)
  DECL_PRED(p, {Int})
  DECL_CONST(a, Int) 
  DECL_POLY_CONST(h, 1, alpha)
  DECL_SORT(A)

  index->insert(1 + a, p(1 + a), unit(p(a + a)));
  index->insert(h(Int), p(h(Int)), unit(p(h(Int))));

  checkTermMatches(*index, h(alpha), Stack<TermUnificationResultSpec>{

        TermUnificationResultSpec 
        { .querySigma  = h(Int),
          .resultSigma = h(Int),
          .constraints = Stack<Literal*>{  } }, 

        TermUnificationResultSpec 
        { .querySigma  = h(Int),
          .resultSigma = 1 + a,
          .constraints = { 1 + a != h(Int), } }, 

      });

  checkTermMatches(*index, h(A), Stack<TermUnificationResultSpec>{ });
}


#define POLY_INT_SUGAR                                                                              \
  DECL_DEFAULT_VARS                                                                                 \
  DECL_DEFAULT_SORT_VARS                                                                            \
  NUMBER_SUGAR(Int)                                                                                 \
  DECL_POLY_CONST(b, 1, alpha)                                                                      \
  DECL_POLY_CONST(a, 1, alpha)                                                                      \
  DECL_POLY_FUNC(f, 1, {alpha}, alpha)                                                              \
  DECL_SORT(A)                                                                                      \
  DECL_CONST(someA, A)                                                                              \


#define HOL_SUGAR(...)                                                                              \
  DECL_DEFAULT_VARS                                                                                 \
  DECL_DEFAULT_SORT_VARS                                                                            \
  NUMBER_SUGAR(Int)                                                                                 \
  DECL_SORT(srt)                                                                                    \
  __VA_ARGS__

 
RUN_TEST(term_indexing_poly_uwa_01,
    POLY_INT_SUGAR,
    IndexTest {
      .index = getTermIndex(),
      .uwa = "one_side_interpreted",
      .insert = {
        f(alpha, a(alpha)),
        f(alpha, b(alpha)),
        f(A, someA),
        f(A, a(A)),
      },
      .query = f(Int, a(Int) + x),
      .expected =  {

        TermUnificationResultSpec 
        { .querySigma  = f(Int, a(Int) + x),
          .resultSigma = f(Int, a(Int)),
          .constraints = { a(Int) != a(Int) + x } }, 

        TermUnificationResultSpec 
        { .querySigma  = f(Int, a(Int) + y),
          .resultSigma = f(Int, b(Int)),
          .constraints = { b(Int) != a(Int) + y } }, 

      }
    })


TEST_FUN(term_indexing_interp_only)
{
  env.options->set("unification_with_abstraction", "interpreted_only");
  env.options->set("unification_with_abstraction_postpro", "off");

  auto index = getTermIndex();

  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Int)
  DECL_PRED(p, {Int})

  DECL_CONST(a, Int) 
  DECL_CONST(b, Int) 

  index->insert(num(1) + num(1), p(num(1) + num(1)), unit(p(num(1) + num(1))));
  index->insert(1 + a, p(1 + a), unit(p(a + a)));

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

  index->insert(a,p(a),unit(p(a)));

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
  env.options->set("unification_with_abstraction", "one_side_interpreted");
  env.options->set("unification_with_abstraction_postpro", "off");

  auto index = getLiteralIndex();

  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Int)
  DECL_PRED(p, {Int})

  DECL_CONST(a, Int) 
  DECL_CONST(b, Int) 

  index->insert(p(num(1) + num(1)), unit(p(num(1) + num(1))));
  index->insert(p(1 + a), unit(p(1 + a)));  

  checkLiteralMatches(*index, p(b + 2), {

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

  checkLiteralMatches(*index, p(b + 2), {

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

#if VHOL

TEST_FUN(higher_order)
{
  DECL_DEFAULT_VARS
  DECL_DEFAULT_SORT_VARS  
  DECL_SORT(srt) 
  DECL_CONST(a, arrow(srt, srt))
  DECL_CONST(b, arrow(srt, srt))
  DECL_CONST(c, srt)
  DECL_CONST(d, srt)    
  DECL_CONST(f, arrow(arrow(srt, srt), srt))
  DECL_CONST(g, arrow(srt, arrow(srt, srt)))

  env.property->forceHigherOrder();

  env.options->set("pretty_hol_printing","pretty");
  env.options->set("func_ext", "abstraction");
  auto index = getTermIndex();

  index->insert(ap(f,a), 0, 0);

  checkHigherOrderTermMatches(*index, ap(f,b), Stack<TermUnificationResultSpec>{

        TermUnificationResultSpec 
        { .querySigma  = ap(f,b),
          .resultSigma = ap(f,a),
          .constraints = Stack<Literal*>{a != b } }, 

      });

  index->insert(ap(g,c), 0, 0);
  index->insert(g, 0, 0);

  checkHigherOrderTermMatches(*index, TypedTermList(x, arrow(srt, srt)), Stack<TermUnificationResultSpec>{

        TermUnificationResultSpec 
        { .querySigma  = ap(g,c),
          .resultSigma = ap(g,c),
          .constraints = Stack<Literal*>{} }, 

      });

  checkHigherOrderTermMatches(*index, ap(f,b), Stack<TermUnificationResultSpec>{

        TermUnificationResultSpec 
        { .querySigma  = ap(f,b),
          .resultSigma = ap(f,a),
          .constraints = Stack<Literal*>{ a != b } }, 

      });

  checkHigherOrderTermMatches(*index, ap(g,d), Stack<TermUnificationResultSpec>{

        TermUnificationResultSpec 
        { .querySigma  = ap(g,d),
          .resultSigma = ap(g,c),
          .constraints = Stack<Literal*>{ ap(g,c) != ap(g,d) } }, 

      });
}

TEST_FUN(higher_order2)
{
  env.property->forceHigherOrder();

  env.options->set("pretty_hol_printing","pretty");
  env.options->set("func_ext", "abstraction");
  auto index = getTermIndex();

  DECL_DEFAULT_SORT_VARS  
  DECL_SORT(srt) 

  DECL_CONST(a, srt)
  DECL_HOL_VAR(x, 0, arrow(srt, srt))
  DECL_HOL_VAR(x2, 1, arrow(srt, arrow(srt, srt))) 
  DECL_HOL_VAR(x3, 2, srt)
  DECL_HOL_VAR(z, 3, srt)

  index->insert(ap(x, a), 0, 0);

  auto id     = toDBs(lam(z, z));
  auto conFun = toDBs(lam(z, a));

  checkHigherOrderTermMatches(*index, a, Stack<TermUnificationResultSpec>{

        TermUnificationResultSpec 
        { .querySigma  = a,
          .resultSigma = ap(id,a),
          .constraints =  Stack<Literal*>{} }, 

        TermUnificationResultSpec 
        { .querySigma  = a,
          .resultSigma = ap(conFun,a),
          .constraints =  Stack<Literal*>{} }, 

      });

  index->insert(ap(ap(x2, a), x3), 0, 0);
   
  checkHigherOrderTermMatches(*index, x3, Stack<TermUnificationResultSpec>{

        TermUnificationResultSpec 
        { .querySigma  = ap(ap(x2, a), x3),
          .resultSigma = ap(ap(x2, a), x3),
          .constraints = Stack<Literal*>{} }, 

        TermUnificationResultSpec 
        { .querySigma  = ap(x,a),
          .resultSigma = ap(x,a),
          .constraints = Stack<Literal*>{ } }, 

      });

}

TEST_FUN(higher_order3)
{
  env.property->forceHigherOrder();

  env.options->set("pretty_hol_printing","pretty");
  env.options->set("func_ext", "abstraction");
  auto index = getTermIndex();

  DECL_DEFAULT_SORT_VARS  
  DECL_SORT(srt) 

  DECL_CONST(a, arrow(srt,srt))
  DECL_CONST(f, arrow(arrow(srt,srt), srt))
  DECL_HOL_VAR(x, 0, srt)

  auto lamTerm = toDBs(lam(x, ap(a, x)));
  auto t = ap(f, lamTerm);

  index->insert(t, 0, 0);

  checkHigherOrderTermMatches(*index, ap(f,a), Stack<TermUnificationResultSpec>{

        TermUnificationResultSpec 
        { .querySigma  = ap(f,a),
          .resultSigma = toDBs(ap(f, lam(x, ap(a, x)))),
          .constraints = Stack<Literal*>{ a != lamTerm  } }, 

      });
}

TEST_FUN(higher_order4)
{
  env.property->forceHigherOrder();

  env.options->set("pretty_hol_printing","pretty");
  env.options->set("func_ext", "abstraction");
  auto index = getTermIndex();

  DECL_DEFAULT_SORT_VARS  
  DECL_SORT(srt) 

  DECL_CONST(a, srt)
  DECL_CONST(g, arrow(srt,srt))
  DECL_CONST(f, arrow(arrow(srt,srt), arrow(srt, srt)))
  DECL_HOL_VAR(x, 0, arrow(srt,srt))


  auto t = ap(ap(f, g), a);

  index->insert(t, 0, 0);

  checkHigherOrderTermMatches(*index, ap(ap(f, x), ap(x,a)), Stack<TermUnificationResultSpec>{
      });
}

TEST_FUN(higher_order5)
{
  env.property->forceHigherOrder();

  env.options->set("pretty_hol_printing","pretty");
  env.options->set("func_ext", "abstraction");
  auto index = getTermIndex();

  DECL_DEFAULT_SORT_VARS  
  DECL_SORT(srt) 

  DECL_CONST(a, srt)
  DECL_CONST(g, arrow(srt,srt))
  DECL_CONST(f, arrow(arrow(srt,srt), arrow(srt, srt)))
  DECL_HOL_VAR(x, 0, arrow(srt,srt))


  auto t = ap(ap(f, g), a);

  index->insert(t, 0, 0);

  checkHigherOrderTermMatches(*index, ap(ap(f, x), ap(x,a)), Stack<TermUnificationResultSpec>{

      });
}


TEST_FUN(higher_order6)
{
  env.property->forceHigherOrder();

  env.options->set("pretty_hol_printing","pretty");
  env.options->set("func_ext", "abstraction");
  auto index = getTermIndex();

  DECL_DEFAULT_SORT_VARS  
  DECL_SORT(srt) 

  DECL_CONST(f, arrow(srt, arrow(srt, srt)))
  DECL_HOL_VAR(x0, 0, arrow(srt, srt))
  DECL_HOL_VAR(x1, 1, srt)

  DECL_HOL_VAR(x, 10, srt)
  DECL_HOL_VAR(z, 11, srt)
  DECL_HOL_VAR(y, 12, arrow(srt, srt))

  auto t = ap(ap(f, x), x);

  index->insert(t, 0, 0);

  checkHigherOrderTermMatches(*index, ap(ap(f, ap(y,z)), z), Stack<TermUnificationResultSpec>{

    TermUnificationResultSpec 
    { .querySigma  = ap(ap(f, ap(x0,x1)), x1),
      .resultSigma = ap(ap(f, x1), x1),
      .constraints = { ap(x0,x1) != x1  } }, 

  });
}

TEST_FUN(higher_order7)
{
  env.property->forceHigherOrder();

  env.options->set("pretty_hol_printing","pretty");
  env.options->set("func_ext", "abstraction");
  auto index = getTermIndex();

  DECL_DEFAULT_SORT_VARS  
  DECL_SORT(srt) 

  DECL_CONST(f, arrow(srt, arrow(srt, srt)))
  DECL_CONST(g, arrow(srt, srt))  
  DECL_HOL_VAR(x, 0, srt)
  DECL_HOL_VAR(z, 1, srt)

  auto t = ap(ap(f, x), x);

  index->insert(t, 0, 0);

  checkHigherOrderTermMatches(*index, ap(ap(f, ap(g,z)), z), Stack<TermUnificationResultSpec>{
  });
}

TEST_FUN(higher_order8)
{
  env.property->forceHigherOrder();

  env.options->set("pretty_hol_printing","pretty");
  env.options->set("func_ext", "abstraction");
  env.options->set("print_var_banks", "true");  
  auto index = getTermIndex();

  DECL_DEFAULT_SORT_VARS  
  DECL_SORT(srt) 

  DECL_CONST(a, srt)  
  DECL_CONST(g, arrow(srt,srt)) 

  DECL_HOL_VAR(x, 10, arrow(srt,srt))
  DECL_HOL_VAR(z, 11, arrow(srt,srt))

  DECL_HOL_VAR(z2, 12, srt)
  DECL_HOL_VAR(z3, 13, srt)

  auto id     = toDBs(lam(z2, z2));
  auto conFun = toDBs(lam(z2, a));

  auto b1     = toDBs(lam(z3, ap(g, ap(id, z3))));
  auto b2     = toDBs(lam(z3, ap(g, ap(conFun, z3))));

  index->insert(ap(x,a), 0, 0);
  index->insert(ap(z,a), 0, 0);
  index->insert(ap(g,ap(z, a)), 0, 0);


  checkHigherOrderTermMatches(*index, ap(g,a), Stack<TermUnificationResultSpec>{

    TermUnificationResultSpec 
    { .querySigma  = ap(g,a),
      .resultSigma = ap(b1,a),
      .constraints = Stack<Literal*>{ } }, 

    TermUnificationResultSpec 
    { .querySigma  = ap(g,a),
      .resultSigma = ap(b2,a),
      .constraints = Stack<Literal*>{ } }, 

    TermUnificationResultSpec 
    { .querySigma  = ap(g,a),
      .resultSigma = ap(b1,a),
      .constraints = Stack<Literal*>{ } }, 

    TermUnificationResultSpec 
    { .querySigma  = ap(g,a),
      .resultSigma = ap(b2,a),
      .constraints = Stack<Literal*>{ } }, 

    TermUnificationResultSpec 
    { .querySigma  = ap(g,a),
      .resultSigma = ap(g,ap(id,a)), //really irritating variable renaming...
      .constraints = Stack<Literal*>{ } }, 

    TermUnificationResultSpec 
    { .querySigma  = ap(g,a),
      .resultSigma = ap(g,ap(conFun,a)), //really irritating variable renaming...
      .constraints = Stack<Literal*>{ } }, 

  });
}

// AYB not a real test, but if run with debugging info
// in HOLSubstitutionTree, very useful for ensuring
// that insertions and deletions are taking place correctly
/*TEST_FUN(higher_order_tree)
{
  env.property->forceHigherOrder();

  env.options->set("pretty_hol_printing","pretty");
  env.options->set("func_ext", "abstraction");
  auto index = getTermIndex();

  DECL_DEFAULT_SORT_VARS  
  DECL_SORT(srt) 

  DECL_CONST(a, arrow(srt,srt))
  DECL_CONST(b, srt)  
  DECL_CONST(d, arrow(srt, arrow(srt, srt)))  
  DECL_CONST(e, srt)    
  DECL_CONST(f, arrow(arrow(srt,srt), srt))
  DECL_HOL_VAR(x, 0, srt)
  DECL_HOL_VAR(y, 1, arrow(srt,srt))
  DECL_HOL_VAR(z, 2, arrow(srt,srt))
  DECL_BOOL_SORT(bools);
  DECL_CONST(p, arrow(srt,bools))  
  DECL_CONST(g, arrow(bools,srt))  


  auto t = ap(f, lam(x, ap(a, x)));
  t = toDBs(t);
  auto t2 = ap(f,lam(x, b));
  t2 = toDBs(t2);

  index->insert(t, 0, 0);
  index->insert(t2, 0, 0);

  index->remove(t2, 0, 0);
  index->remove(t, 0, 0);

  index->insert(ap(y,b), 0, 0);
  index->insert(ap(y, ap(a,b)), 0, 0);
  index->insert(ap(z, ap(a,b)), 0, 0);

  index->remove(ap(y,b), 0, 0);
  index->remove(ap(y, ap(a,b)), 0, 0);
  index->remove(ap(z, ap(a,b)), 0, 0);

  index->insert(ap(f,ap(d,b)), 0, 0);
  index->insert(ap(f,ap(d,e)), 0, 0);  

  index->remove(ap(f,ap(d,b)), 0, 0);
  index->remove(ap(f,ap(d,e)), 0, 0);  

  index->insert(ap(p,b), 0, 0);
  index->insert(ap(p,e), 0, 0);  

  index->remove(ap(p,b), 0, 0);
  index->remove(ap(p,e), 0, 0);  

  index->insert(ap(g, ap(p,b)), 0, 0);
  index->insert(ap(g, ap(p,e)), 0, 0);  
}*/

#endif

Option<TermUnificationResultSpec> runRobUnify(TermList a, TermList b, Options::UnificationWithAbstraction opt, bool fixedPointIteration) {

  Kernel::UnificationAlgorithms::AbstractingUnification au(MismatchHandler(opt), fixedPointIteration);
  
  static Kernel::RobSubstitutionTL subst;
  subst.reset();

  auto unifs = au.unifiers(a, b, &subst);

  if (unifs.hasNext()) {
    Kernel::RobSubstitutionTL* sub = unifs.next();
    return some(TermUnificationResultSpec { 
     .querySigma  = sub->apply(a, DEFAULT_BANK), 
     .resultSigma = sub->apply(b, DEFAULT_BANK), 
     .constraints = *sub->constraints(),
    });
  } else {
    return {};
  }
}

void checkRobUnify(TermList a, TermList b, Options::UnificationWithAbstraction opt, bool fixedPointIteration, TermUnificationResultSpec exp)
{
  auto is = runRobUnify(a,b,opt, fixedPointIteration);
  if (is.isSome() && is.unwrap() == exp) {
    cout << "[  OK  ] " << a << " unify " << b << endl;
  } else {
    cout << "[ FAIL ] " << a << " unify " << b << endl;
    cout << "is:       " << is << endl;
    cout << "expected: " << exp << endl;
    exit(-1);
  }
}

void checkRobUnifyFail(TermList a, TermList b, Options::UnificationWithAbstraction opt, bool fixedPointIteration)
{
  auto is = runRobUnify(a,b,opt, fixedPointIteration);
  if(is.isNone()) {
      cout << "[  OK  ] " << a << " unify " << b << endl;
  } else {
    cout << "[ FAIL ] " << a << " unify " << b << endl;
    cout << "is:       " << is << endl;
    cout << "expected: nothing" << endl;
    exit(-1);
  }
}

#define ROB_UNIFY_TEST(name, opt, fixedPointIteration, lhs, rhs, ...)                                          \
  TEST_FUN(name)                                                                                    \
  {                                                                                                 \
    INT_SUGAR                                                                                       \
    checkRobUnify(lhs, rhs, opt, fixedPointIteration, __VA_ARGS__ );                                           \
  }                                                                                                 \

#define ROB_UNIFY_TEST_FAIL(name, opt, fixedPointIteration, lhs, rhs)                                          \
  TEST_FUN(name)                                                                                    \
  {                                                                                                 \
    INT_SUGAR                                                                                       \
    checkRobUnifyFail(lhs, rhs, opt, fixedPointIteration);                                                     \
  }                                                                                                 \

ROB_UNIFY_TEST(rob_unif_test_01,
    Options::UnificationWithAbstraction::ONE_INTERP,
    /* withFinalize */ false,
    f(b + 2), 
    f(x + 2),
    TermUnificationResultSpec { 
      .querySigma = f(b + 2),
      .resultSigma = f(x + 2),
      .constraints = { x + 2 != b + 2 },
    })

ROB_UNIFY_TEST(rob_unif_test_02,
    Options::UnificationWithAbstraction::ONE_INTERP,
    /* withFinalize */ false,
    f(b + 2), 
    f(x + 2),
    TermUnificationResultSpec { 
      .querySigma = f(b + 2),
      .resultSigma = f(x + 2),
      .constraints = { x + 2 != b + 2 },
    })

ROB_UNIFY_TEST(rob_unif_test_03,
    Options::UnificationWithAbstraction::ONE_INTERP,
    /* withFinalize */ false,
    f(x + 2), 
    f(a),
    TermUnificationResultSpec { 
      .querySigma = f(x + 2),
      .resultSigma = f(a),
      .constraints = { x + 2 != a },
    })

ROB_UNIFY_TEST_FAIL(rob_unif_test_04,
    Options::UnificationWithAbstraction::ONE_INTERP,
    /* withFinalize */ false,
    f(a), g(1 + a))


ROB_UNIFY_TEST(rob_unif_test_05,
    Options::UnificationWithAbstraction::ONE_INTERP,
    /* withFinalize */ false,
    f(a + b), 
    f(x + y),
    TermUnificationResultSpec { 
      .querySigma = f(a + b),
      .resultSigma = f(x + y),
      .constraints = { x + y != a + b },
    })

ROB_UNIFY_TEST(rob_unif_test_06,
    Options::UnificationWithAbstraction::ONE_INTERP,
    /* withFinalize */ false,
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
    /* withFinalize */ false,
    f2(x, a + x),
    f2(c, b + a),
    TermUnificationResultSpec { 
      .querySigma  = f2(c, a + c),
      .resultSigma = f2(c, b + a),
      .constraints = { c != b },
    })

ROB_UNIFY_TEST_FAIL(over_approx_test_2_bad_AC1_fixedPointIteration,
    Options::UnificationWithAbstraction::AC1,
    /* withFinalize */ true,
    f2(x, a + x),
    f2(c, b + a)
    )

ROB_UNIFY_TEST_FAIL(over_approx_test_2_good_AC1,
    Options::UnificationWithAbstraction::AC1,
    /* withFinalize */ false,
    f2(a + x, x),
    f2(b + a, c))

ROB_UNIFY_TEST(bottom_constraint_test_1_bad_AC1,
    Options::UnificationWithAbstraction::AC1,
    /* withFinalize */ false,
    f2(f2(y, x), a + y + x),
    f2(f2(b, c), c + b + a),
    TermUnificationResultSpec { 
      .querySigma  = f2(f2(b,c), a + b + c),
      .resultSigma = f2(f2(b,c), c + b + a),
      .constraints = Stack<Literal*>{ b + c != c + b },
    })

ROB_UNIFY_TEST(bottom_constraint_test_1_bad_AC1_fixedPointIteration,
    Options::UnificationWithAbstraction::AC1,
    /* withFinalize */ true,
    f2(f2(y, x), a + y + x),
    f2(f2(b, c), c + b + a),
    TermUnificationResultSpec { 
      .querySigma  = f2(f2(b,c), a + b + c),
      .resultSigma = f2(f2(b,c), c + b + a),
      .constraints = Stack<Literal*>{  },
    })

ROB_UNIFY_TEST(bottom_constraint_test_1_good_AC1,
    Options::UnificationWithAbstraction::AC1,
    /* withFinalize */ false,
    f2(a + x + y, f2(x, y)),
    f2(c + b + a, f2(b, c)),
    // f2(a + x, x),
    // f2(b + a, b),
    TermUnificationResultSpec { 
      .querySigma  = f2(a + b + c, f2(b,c)),
      .resultSigma = f2(c + b + a, f2(b,c)),
      .constraints = Stack<Literal*>{},
    })


ROB_UNIFY_TEST(ac_bug_01,
    Options::UnificationWithAbstraction::AC1,
    /* withFinalize */ false,
    a + b + c + a,
    a + b + x + y,
    TermUnificationResultSpec { 
      .querySigma  = a + b + c + a,
      .resultSigma = a + b + x + y,
      .constraints = { c + a != x + y },
    })

ROB_UNIFY_TEST(ac_test_01_AC1,
    Options::UnificationWithAbstraction::AC1,
    /* withFinalize */ false,
    f2(b, a + b + c),
    f2(b, x + y + c),
    TermUnificationResultSpec { 
      .querySigma  = f2(b, a + b + c),
      .resultSigma = f2(b, x + y + c),
      .constraints = { a + b != x + y },
    })

ROB_UNIFY_TEST(ac_test_02_AC1_good,
    Options::UnificationWithAbstraction::AC1,
    /* withFinalize */ false,
    f2(a + b + c, c),
    f2(x + y + z, z),
    TermUnificationResultSpec { 
      .querySigma  = f2(a + b + c, c),
      .resultSigma = f2(x + y + c, c),
      .constraints = { a + b != x + y },
    })

ROB_UNIFY_TEST(ac_test_02_AC1_bad,
    Options::UnificationWithAbstraction::AC1,
    /* withFinalize */ false,
    f2(c, a + b + c),
    f2(z, x + y + z),
    TermUnificationResultSpec { 
      .querySigma  = f2(c, a + b + c),
      .resultSigma = f2(c, x + y + c),
      .constraints = { a + b + c != x + y + c },
    })

ROB_UNIFY_TEST(ac_test_02_AC1_bad_fixedPointIteration,
    Options::UnificationWithAbstraction::AC1,
    /* withFinalize */ true,
    f2(c, a + b + c),
    f2(z, x + y + z),
    TermUnificationResultSpec { 
      .querySigma  = f2(c, a + b + c),
      .resultSigma = f2(c, x + y + c),
      .constraints = { a + b != x + y },
    })

ROB_UNIFY_TEST(ac2_test_01,
    Options::UnificationWithAbstraction::AC2,
    /* withFinalize */ false,
    f2(x, a + b + c),
    f2(x, x + b + a),
    TermUnificationResultSpec { 
      .querySigma  = f2(c, a + b + c),
      .resultSigma = f2(c, c + b + a),
      .constraints = Stack<Literal*>{},
    })

ROB_UNIFY_TEST(ac2_test_02,
    Options::UnificationWithAbstraction::AC2,
    /* withFinalize */ false,
    f2(a + b + c, f2(x,b)),
    f2(x + y + a, f2(x,y)),
    TermUnificationResultSpec { 
      .querySigma  = f2(a + b + c, f2(c,b)),
      .resultSigma = f2(c + b + a, f2(c,b)),
      .constraints = Stack<Literal*>{},
    })

ROB_UNIFY_TEST(ac2_test_02_bad,
    Options::UnificationWithAbstraction::AC2,
    /* withFinalize */ false,
    f2(f2(x,b), a + b + c),
    f2(f2(x,y), x + y + a),
    TermUnificationResultSpec { 
      .querySigma  = f2(f2(x,b), a + b + c),
      .resultSigma = f2(f2(x,b), x + b + a),
      .constraints = Stack<Literal*>{ b + c != x + b },
    })

ROB_UNIFY_TEST(ac2_test_02_bad_fixedPointIteration,
    Options::UnificationWithAbstraction::AC2,
    /* withFinalize */ true,
    f2(f2(x,b), a + b + c),
    f2(f2(x,y), x + y + a),
    TermUnificationResultSpec { 
      .querySigma  = f2(f2(c,b), a + b + c),
      .resultSigma = f2(f2(c,b), c + b + a),
      .constraints = Stack<Literal*>{ },
    })


ROB_UNIFY_TEST(top_level_constraints_1,
    Options::UnificationWithAbstraction::AC2,
    /* withFinalize */ false,
    a + y + x,
    a + b + c,
    TermUnificationResultSpec { 
      .querySigma  = a + y + x,
      .resultSigma = a + b + c,
      .constraints = Stack<Literal*>{ b + c != x + y },
    })

RUN_TEST(top_level_constraints_2_with_fixedPointIteration,
    INT_SUGAR,
    IndexTest {
      .index = getTermIndex(),
      .uwa = "ac2",
      .fixedPointIteration = "on",
      .insert = {
        a + b + c,
        b,
        a + b + f(a) + c,
        f(x),
        f(a),
      },
      .query = a + y + x,
      .expected = { 

          TermUnificationResultSpec 
          { .querySigma  = a + x0 + x1,
            .resultSigma = a + b + c,
            .constraints = Stack<Literal*>{ b + c != x1 + x0 } }, 

          TermUnificationResultSpec 
          { .querySigma  = a + x2 + x3,
            .resultSigma = a + b + f(a) + c,
            .constraints = Stack<Literal*>{ b + f(a) + c != x3 + x2 } }, 

      },
    })


RUN_TEST(top_level_constraints_2,
    INT_SUGAR,
    IndexTest {
      .index = getTermIndex(),
      .uwa = "ac2",
      .insert = {
        a + b + c,
        b,
        a + b + a + c,
        f(x),
        f(a),
      },
      .query = a + y + x,
      .expected = { 

          TermUnificationResultSpec 
          { .querySigma  = a + x0 + x1,
            .resultSigma = a + b + c,
            .constraints = Stack<Literal*>{ a + b + c != a + x1 + x0 } }, 

          TermUnificationResultSpec 
          { .querySigma  = a + x2 + x3,
            .resultSigma = a + b + a + c,
            .constraints = Stack<Literal*>{ a + b + a + c != a + x3 + x2 } }, 

      },
    })
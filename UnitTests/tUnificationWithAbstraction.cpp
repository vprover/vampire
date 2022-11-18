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

Stack<Literal*> constraintLits(Stack<UnificationConstraint>& cnst, RobSubstitution& subs) {

  auto constraintLit = [&](UnificationConstraint c) {
    auto createTerm = [&](auto x) 
      { return subs.apply(x.first, x.second); };
    auto s = createTerm(c.first);
    auto t = createTerm(c.second);
    TermList srt = SortHelper::getResultSort(s.isTerm() ? s.term() : t.term());
    return Literal::createEquality(false, s,t,srt);
  };
  return iterTraits(cnst.iterFifo())
       .map([&](auto c) { return constraintLit(c); })
       .collect<Stack>();
}


TermIndexingStructure* getTermIndexHOL()
{ 
  // env.options->setUWA(Shell::Options::UnificationWithAbstraction::)
  // env.options.set("")
  // return new TermSubstitutionTree(true);
  TODO
}

TermIndexingStructure* getTermIndex(Shell::Options::UnificationWithAbstraction uwa)
{ 
  env.options->setUWA(uwa);
  return new TermSubstitutionTree(true);
}

LiteralIndexingStructure* getLiteralIndex(Shell::Options::UnificationWithAbstraction uwa)
{
  TODO
}

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



void checkLiteralMatches(LiteralIndexingStructure* index, Literal* lit, Stack<LiteralUnificationResultSpec> expected)
{
  Stack<LiteralUnificationResultSpec> is;
  for (auto qr : iterTraits(index->getUnifications(lit,false,true)) ) {
    // qr.substitution->numberOfConstraints();

    is.push(LiteralUnificationResultSpec {
        .querySigma = qr.substitution->apply(lit, /* result */ false),
        .resultSigma = qr.substitution->apply(qr.literal, /* result */ true),
        .constraints = constraintLits(*qr.constraints, *qr.substitution->tryGetRobSubstitution()),
    });
  }
  if (Test::TestUtils::permEq(is, expected, [](auto& l, auto& r) { return l == r; })) {
    cout << "[  OK  ] " << *lit << endl;
  } else {
    cout << "[ FAIL ] " << *lit << endl;

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
void checkTermMatches(TermIndexingStructure* index, TermList term, TermList sort, Stack<TermUnificationResultSpec> expected)
{
  Stack<TermUnificationResultSpec> is;
  for (auto qr : iterTraits(index->getUnificationsUsingSorts(term,sort,true)) ) {

    is.push(TermUnificationResultSpec {
        .querySigma = qr.substitution->apply(term, /* result */ false),
        .resultSigma = qr.substitution->apply(qr.term, /* result */ true),
        .constraints = constraintLits(*qr.constraints, *qr.substitution->tryGetRobSubstitution()),
    });
  }
  if (Test::TestUtils::permEq(is, expected, [](auto& l, auto& r) { return l == r; })) {
    cout << "[  OK  ] " << term << endl;
  } else {
    cout << "[ FAIL ] " << term << endl;
    cout << "tree: " << *index;
    cout << "query: " << term << ": " << sort;

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

TEST_FUN(term_indexing_one_side_interp)
{
  TermIndexingStructure* index = getTermIndex(Options::UnificationWithAbstraction::ONE_INTERP);

  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Int)
  DECL_PRED(p, {Int})
  DECL_FUNC(f, {Int}, Int)
  DECL_CONST(a, Int) 
  DECL_CONST(b, Int) 

  index->insert(num(1) + num(1), p(num(1) + num(1)), unit(p(num(1) + num(1))));
  index->insert(1 + a, p(1 + a), unit(p(a + a)));
  
  checkTermMatches(index, b + 2, Int,
      { 

        TermUnificationResultSpec 
        { .querySigma  = 2 + b,
          .resultSigma = 1 + a,
          .constraints = { 1 + a != 2 + b, } },

        TermUnificationResultSpec 
        { .querySigma  = 2 + b,
          .resultSigma = 1 + num(1),
          .constraints = { 2 + b != 1 + num(1), } }, 

      });

  index->insert(a,p(a),unit(p(a)));

  checkTermMatches(index,b + 2, Int, {

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

      });


  checkTermMatches(index, x, Int, {

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

      });


  index->insert(f(x),p(f(x)),unit(p(f(x))));

  checkTermMatches(index, f(a), Int, {

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

      });

  checkTermMatches(index, a + 3, Int, {

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

      }); 
}

TEST_FUN(term_indexing_poly)
{
  TermIndexingStructure* index = getTermIndex(Options::UnificationWithAbstraction::ONE_INTERP);

  DECL_DEFAULT_VARS
  DECL_DEFAULT_SORT_VARS  
  NUMBER_SUGAR(Int)
  DECL_PRED(p, {Int})
  DECL_CONST(a, Int) 
  DECL_POLY_CONST(h, 1, alpha)
  DECL_SORT(A)

  index->insert(1 + a, p(1 + a), unit(p(a + a)));
  index->insert(h(Int), p(h(Int)), unit(p(h(Int))));

  checkTermMatches(index, h(alpha), alpha, Stack<TermUnificationResultSpec>{

        TermUnificationResultSpec 
        { .querySigma  = h(Int),
          .resultSigma = h(Int),
          .constraints = Stack<Literal*>{  } }, 

        TermUnificationResultSpec 
        { .querySigma  = h(Int),
          .resultSigma = 1 + a,
          .constraints = { 1 + a != h(Int), } }, 

      });

  checkTermMatches(index, h(A), A, Stack<TermUnificationResultSpec>{ });
}

TEST_FUN(term_indexing_interp_only)
{
  TermIndexingStructure* index = getTermIndex(Options::UnificationWithAbstraction::INTERP_ONLY);

  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Int)
  DECL_PRED(p, {Int})

  DECL_CONST(a, Int) 
  DECL_CONST(b, Int) 

  index->insert(num(1) + num(1), p(num(1) + num(1)), unit(p(num(1) + num(1))));
  index->insert(1 + a, p(1 + a), unit(p(a + a)));

  checkTermMatches(index,b + 2,Int,{

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

  checkTermMatches(index,b + 2,Int, {

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
  LiteralIndexingStructure* index = getLiteralIndex(Options::UnificationWithAbstraction::ONE_INTERP);

  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Int)
  DECL_PRED(p, {Int})

  DECL_CONST(a, Int) 
  DECL_CONST(b, Int) 

  index->insert(p(num(1) + num(1)), unit(p(num(1) + num(1))));
  index->insert(p(1 + a), unit(p(1 + a)));  


  checkLiteralMatches(index,p(b + 2),{

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

  checkLiteralMatches(index,p(b + 2),{

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
  TermIndexingStructure* index = getTermIndexHOL();

  DECL_DEFAULT_VARS
  DECL_DEFAULT_SORT_VARS  
  NUMBER_SUGAR(Int)
  DECL_SORT(srt) 
  DECL_ARROW_SORT(xSrt, {srt, srt}) 
  DECL_ARROW_SORT(fSrt, {xSrt, srt}) 
  DECL_ARROW_SORT(gSrt, {srt, xSrt})   
  DECL_HOL_VAR(x0, 0, xSrt)
  DECL_CONST(a, xSrt)
  DECL_CONST(b, xSrt)
  DECL_CONST(c, srt)  
  DECL_CONST(f, fSrt)
  DECL_CONST(g, gSrt)
  DECL_POLY_CONST(h, 1, alpha)

  index->insert(ap(f,a), 0, 0);

  checkTermMatches(index,ap(f,b),srt, Stack<TermUnificationResultSpec>{

        TermUnificationResultSpec 
        { .querySigma  = ap(f,b),
          .resultSigma = ap(f,a),
          .constraints = { a != b, } }, 

      });

  index->insert(ap(g,c), 0, 0);
  index->insert(g, 0, 0);

  // TODO
  // reportTermMatches(index,x0,xSrt);

  index->insert(h(alpha), 0, 0);

  // TODO
  // reportTermMatches(index,h(beta),beta);
  // reportTermMatches(index,h(srt),srt);
}

TEST_FUN(higher_order2)
{
  TermIndexingStructure* index = getTermIndexHOL();

  DECL_DEFAULT_VARS
  DECL_DEFAULT_SORT_VARS  
  NUMBER_SUGAR(Int)
  DECL_SORT(srt) 
  DECL_ARROW_SORT(xSrt, {srt, srt}) 
  DECL_ARROW_SORT(fSrt, {xSrt, xSrt, srt}) 
  DECL_CONST(a, xSrt)
  DECL_CONST(b, xSrt)
  DECL_CONST(f, fSrt)

  index->insert(ap(ap(f,a),b), 0, 0);

  // TODO
  // reportTermMatches(index,ap(ap(f,b),a),srt);
}

static const int NORM_QUERY_BANK=2;
static const int NORM_RESULT_BANK=3;

Option<TermUnificationResultSpec> runRobUnify(TermList a, TermList b, Options::UnificationWithAbstraction opt) {
  Stack<UnificationConstraint> cnst;
  UWAMismatchHandler h(cnst);
  RobSubstitution subs;
  bool result = subs.unify(a,NORM_QUERY_BANK,b,NORM_RESULT_BANK);
  if (result) {

    return some(TermUnificationResultSpec { 
     .querySigma  = subs.apply(a, NORM_QUERY_BANK), 
     .resultSigma = subs.apply(b, NORM_RESULT_BANK), 
     .constraints = constraintLits(cnst, subs),
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

#define DEFAULT_SUGAR                                                                               \
    __ALLOW_UNUSED(                                                                                 \
      DECL_DEFAULT_VARS                                                                             \
      NUMBER_SUGAR(Int)                                                                             \
      DECL_FUNC(f, {Int}, Int)                                                                      \
      DECL_FUNC(g, {Int}, Int)                                                                      \
      DECL_CONST(a, Int)                                                                            \
      DECL_CONST(b, Int)                                                                            \
    ) 

#define ROB_UNIFY_TEST(name, opt, lhs, rhs, ...)                                                    \
  TEST_FUN(name)                                                                                    \
  {                                                                                                 \
    DEFAULT_SUGAR                                                                                   \
    checkRobUnify(lhs, rhs, opt, __VA_ARGS__ );                                                     \
  }                                                                                                 \

#define ROB_UNIFY_TEST_FAIL(name, opt, lhs, rhs)                                                    \
  TEST_FUN(name)                                                                                    \
  {                                                                                                 \
    DEFAULT_SUGAR                                                                                   \
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

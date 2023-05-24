/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#if VHOL

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
#include "Shell/LambdaConversion.hpp"

#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"

#include <ios>


using namespace Kernel;
using namespace Indexing;

#define TODO ASSERTION_VIOLATION_REP("TODO")

TypedTermList toDeBrs(TermList t){
  CALL("toDeBrs");
  ASS(!t.isVar());

  auto converted = LambdaConversion().convertLambda(t);
  auto sort =      SortHelper::getResultSort(converted.term());
  return TypedTermList(converted, sort);
}

Clause* unt(Literal* lit)
{
  return clause({ lit });
}

unique_ptr<TermSubstitutionTree> getIndexTerm()
{ return std::make_unique<TermSubstitutionTree>(SplittingAlgo::HOL_MATCH); }

auto getIndexLiteral()
{ return std::make_unique<LiteralSubstitutionTree>(); }

template<class TermOrLit>
struct MatchingResultSpec {
  TermOrLit querySigma;
  TermOrLit resultSigma;

  friend bool operator==(MatchingResultSpec const& l, MatchingResultSpec const& r)
  {
    return Test::TestUtils::eqModAC(l.querySigma, r.querySigma)
       &&  Test::TestUtils::eqModAC(l.resultSigma, r.resultSigma);
  }

  friend std::ostream& operator<<(std::ostream& out, MatchingResultSpec const& self)
  { 
    return out << "{ querySigma = " << Test::pretty(self.querySigma) << ", resultSigma = " << Test::pretty(self.resultSigma);
  }
};

using TermMatchingResultSpec    = MatchingResultSpec<TermList>;
using LiteralMatchingResultSpec = MatchingResultSpec<Literal*>;

template<class F>
void checkLiteralMatches(LiteralSubstitutionTree& index, Literal* lit, Stack<TermMatchingResultSpec> expected, F unifFun)
{
  Stack<TermMatchingResultSpec> is;
  for (auto qr : iterTraits(unifFun(index, lit)) ) {
    is.push(TermMatchingResultSpec {
        .querySigma = qr.unifier->apply(lit, QUERY_BANK),
        .resultSigma = qr.unifier->apply(qr.literal, RESULT_BANK)
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

void checkTermMatches(TermSubstitutionTree& index, TypedTermList term, Stack<TermMatchingResultSpec> expected, bool instances)
{
  CALL("checkTermMatchesWithUnifFun(TermSubstitutionTree& index, TermList term, Stack<TermMatchingResultSpec> expected, bool instances)")
 
  auto it = iterTraits(instances ?  index.getHOLInstances(term) :  index.getHOLGeneralizations(term)  );

  Stack<TermMatchingResultSpec> is;
  for (auto qr : it) {
    is.push(TermMatchingResultSpec {
        .querySigma  = instances ? qr.unifier->applyTo(term, QUERY_BANK) : term,
        .resultSigma = instances ? qr.term : qr.unifier->applyTo(qr.term, RESULT_BANK)
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

void checkTermInstances(TermSubstitutionTree& index, TypedTermList term, Stack<TermMatchingResultSpec> expected)
{
  checkTermMatches(index, term, expected, true);
}

void checkTermGeneralizations(TermSubstitutionTree& index, TypedTermList term, Stack<TermMatchingResultSpec> expected)
{
  checkTermMatches(index, term, expected,false);
}


struct IndTest {
  unique_ptr<TermSubstitutionTree> index;
  Stack<TypedTermList> insert;
  TermSugar query;
  Stack<TermMatchingResultSpec> expected;
  bool instantiation;

  void run() {
    CALL("IndexTest::run")

    env.property->forceHigherOrder();
    // if printing causes a crash, set this to raw
    // crash happens when attempting to print a loose De Bruijn index
    env.options->set("pretty_hol_printing","pretty");
 
    DECL_PRED(dummy, Stack<SortSugar>())
    for (auto x : this->insert) {
      index->insert(x, dummy(), unt(dummy()));
    }

    if(instantiation){
      checkTermInstances(*this->index, TypedTermList(this->query, this->query.sort()),this->expected);
    } else {
      checkTermGeneralizations(*this->index, TypedTermList(this->query, this->query.sort()),this->expected);      
    }
  }
};


#define HOL_SUGAR                                                                                   \
   __ALLOW_UNUSED(                                                                                  \
      DECL_SORT(srt)                                                                                \
      DECL_DEFAULT_VARS                                                                             \
      DECL_DEFAULT_SORT_VARS                                                                        \
      DECL_HOL_VAR(x0, 0, srt)                                                                      \
      DECL_HOL_VAR(x1, 1, srt)                                                                      \
      DECL_HOL_VAR(y0, 5, srt)                                                                      \
      DECL_HOL_VAR(x2, 2, arrow(srt,srt))                                                           \
      DECL_HOL_VAR(x3, 3, arrow(srt,srt))                                                           \
      DECL_HOL_VAR(x4, 4, arrow(arrow(srt, srt),arrow(srt,srt)))                                    \
      DECL_CONST(a,srt)                                                                             \
      DECL_CONST(b,srt)                                                                             \
      DECL_CONST(c,srt)                                                                             \
      DECL_CONST(f,arrow(srt,srt))                                                                  \
      DECL_CONST(g,arrow(srt,srt))                                                                  \
      DECL_CONST(h,arrow(arrow(srt, srt),arrow(srt,srt)))                                           \
      DECL_CONST(k,arrow(srt,arrow(srt,srt)))                                                       \
    )                                                                                               \
 

#define RUN_TEST(name, sugar, ...)                                                                  \
  TEST_FUN(name) {                                                                                  \
       __ALLOW_UNUSED(sugar)                                                                        \
       __VA_ARGS__.run();                                                                           \
  }                                                                                                 \

RUN_TEST(hol_matching_01,
    HOL_SUGAR,
    IndTest {
      .index = getIndexTerm(),
      .insert = {
        toDeBrs(lam(x1, ap(f, x1))),
      },
      .query = x2,
      .expected = { 

          TermMatchingResultSpec 
          { .querySigma  = toDeBrs(lam(x1, ap(f, x1))),
            .resultSigma = toDeBrs(lam(x1, ap(f, x1))) 
          } 

      },
      .instantiation = true,
    })

RUN_TEST(hol_matching_09,
    HOL_SUGAR,
    IndTest {
      .index = getIndexTerm(),
      .insert = {
        ap(ap(k, ap(g, a) ), ap(g,a) ),
        ap(ap(k, ap(g, c) ), ap(g,b) ),
        ap(ap(k, x1 ), x1 ),
      },
      .query = ap(ap(k, x0 ), x0 ),
      .expected = { 

          TermMatchingResultSpec 
          { .querySigma  = ap(ap(k, ap(g, a) ), ap(g,a) ),
            .resultSigma = ap(ap(k, ap(g, a) ), ap(g,a) )
          } ,

          TermMatchingResultSpec 
          { .querySigma  = ap(ap(k, x1 ), x1 ),
            .resultSigma = ap(ap(k, x1 ), x1 )
          }           

      },
      .instantiation = true,
    })

RUN_TEST(hol_matching_02,
    HOL_SUGAR,
    IndTest {
      .index = getIndexTerm(),
      .insert = {
        ap(x2,a),
      },
      .query = ap(f,a),
      .expected = { 

          TermMatchingResultSpec 
          { .querySigma  = ap(f,a),
            .resultSigma = ap(f,a) 
          } 

      },
      .instantiation = false,
    })

RUN_TEST(hol_matching_03,
    HOL_SUGAR,
    IndTest {
      .index = getIndexTerm(),
      .insert = {
        toDeBrs(ap(ap(x4,lam(x0,x0)), a)),
      },
      .query = toDeBrs(ap(ap(h,lam(x0,x0)), a)),
      .expected = { 

          TermMatchingResultSpec 
          { .querySigma  = toDeBrs(ap(ap(h,lam(x0,x0)), a)),
            .resultSigma = toDeBrs(ap(ap(h,lam(x0,x0)), a)) 
          } 

      },
      .instantiation = false,
    })

RUN_TEST(hol_matching_04,
    HOL_SUGAR,
    IndTest {
      .index = getIndexTerm(),
      .insert = {
        toDeBrs(lam(x0, lam(x1, x0))),
      },
      .query = toDeBrs(lam(x0, lam(x1, x0))),
      .expected = { 

          TermMatchingResultSpec 
          { .querySigma  = toDeBrs(lam(x0, lam(x1, x0))),
            .resultSigma = toDeBrs(lam(x0, lam(x1, x0))) 
          } 

      },
      .instantiation = false,
    })

RUN_TEST(hol_matching_05,
    HOL_SUGAR,
    IndTest {
      .index = getIndexTerm(),
      .insert = {
        toDeBrs(lam(x0, lam(x1, x0))),
      },
      .query = toDeBrs(lam(x0, lam(x1, x1))),
      .expected = Stack<TermMatchingResultSpec>{},
      .instantiation = false,
    })

RUN_TEST(hol_matching_06,
    HOL_SUGAR,
    IndTest {
      .index = getIndexTerm(),
      .insert = {
        toDeBrs(lam(x0, lam(x1, x0))),
      },
      .query = toDeBrs(lam(x0, lam(x1, y0))),
      .expected = Stack<TermMatchingResultSpec>{},
      .instantiation = true,
    })

RUN_TEST(hol_matching_07,
    HOL_SUGAR,
    IndTest {
      .index = getIndexTerm(),
      .insert = {
        ap(ap(k,a),b),
        ap(ap(k,b),b),
      },
      .query = ap(ap(k,x0),x0),
      .expected = { 

          TermMatchingResultSpec 
          { .querySigma  = ap(ap(k,b),b),
            .resultSigma = ap(ap(k,b),b)
          } 

      },    
      .instantiation = true,
  })

RUN_TEST(hol_matching_08,
    HOL_SUGAR,
    IndTest {
      .index = getIndexTerm(),
      .insert = {
        ap(ap(k,a),b),
      },
      .query = ap(ap(k,ap(f, x0)),x0),
      .expected = Stack<TermMatchingResultSpec>{},    
      .instantiation = true,
  })

#endif
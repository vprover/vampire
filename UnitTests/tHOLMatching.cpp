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
      DECL_HOL_VAR(x2, 2, arrow(srt,srt))                                                           \
      DECL_HOL_VAR(x3, 3, arrow(srt,srt))                                                           \
      DECL_CONST(a,srt)                                                                             \
      DECL_CONST(b,srt)                                                                             \
      DECL_CONST(f,arrow(srt,srt))                                                                  \
      DECL_CONST(g,arrow(srt,srt))                                                                  \
    )                                                                                               \
 

#define RUN_TEST(name, sugar, ...)                                                                  \
  TEST_FUN(name) {                                                                                  \
       __ALLOW_UNUSED(sugar)                                                                        \
       __VA_ARGS__.run();                                                                           \
  }                                                                                                 \

RUN_TEST(hol_matching_inst_01,
    HOL_SUGAR,
    IndTest {
      .index = getIndexTerm(),
      .insert = {
        toDeBrs(lam(x1, ap(f, x1))),
      },
      .query = x2,
      .instantiation = true,
      .expected = { 

          TermMatchingResultSpec 
          { .querySigma  = f,
            .resultSigma = toDeBrs(lam(x1, ap(f, x1))) 
          } 

      },
    })


#endif
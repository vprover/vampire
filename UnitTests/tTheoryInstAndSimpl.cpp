
  /*
   * File tGaussianElimination.cpp.
   *
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
#include "Indexing/TermSharing.hpp"
#include "Inferences/GaussianVariableElimination.hpp"
#include "Inferences/InterpretedEvaluation.hpp"
#include "Kernel/Ordering.hpp"
#include "Inferences/PolynomialEvaluation.hpp"
#include "Inferences/Cancellation.hpp"

#include "Test/SyntaxSugar.hpp"
#include "Test/TestUtils.hpp"
#include "Lib/Coproduct.hpp"
#include "Test/GenerationTester.hpp"
#include "Kernel/KBO.hpp"

using namespace std;
using namespace Kernel;
using namespace Inferences;
using namespace Test;

///////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// TEST UNIT INITIALIZATION
/////////////////////////////////////

#define DECL_LIST(sort)                                                                                       \
  DECL_SORT(list)                                                                                             \
                                                                                                              \
  DECL_CONST(nil, list)                                                                                       \
  DECL_FUNC(cons, { sort, list  }, list)                                                                      \
                                                                                                              \
  DECL_TERM_ALGEBRA(list, {nil, cons})                                                                        \
  __ALLOW_UNUSED(                                                                                             \
    auto head = cons.dtor(0);                                                                                 \
    auto tail = cons.dtor(1);                                                                                 \
  )                                                                                                           \

#define MY_SYNTAX_SUGAR                                                                                       \
  NUMBER_SUGAR(Int)                                                                                           \
  DECL_DEFAULT_VARS                                                                                           \
  DECL_FUNC(f, {Int}, Int)                                                                                    \
  DECL_PRED(p, {Int})                                                                                         \
  DECL_PRED(q, {Int})                                                                                         \
  DECL_PRED(r, {Int,Int})                                                                                     \
  DECL_LIST(Int)                                                                                              \

///////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// TEST CASES
/////////////////////////////////////
TheoryInstAndSimp* theoryInstAndSimp(Options::TheoryInstSimp mode) {
  return new TheoryInstAndSimp(mode, 
      /* showZ3 */ true,
      /* unsatCoreForRefutations */ false);
}

using Shell::Int;
REGISTER_GEN_TESTER(Test::Generation::GenerationTester<TheoryInstAndSimp>)

TEST_GENERATION(test_01,
    Generation::TestCase()
      .rule(theoryInstAndSimp(Options::TheoryInstSimp::ALL))
      .input(    clause({  x * y != 6, ~(0 < x), ~(x < y), r(x,y)  }))
      .expected(exactly(
            clause({ r(2,3)  })
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION(test_02,
    Generation::TestCase()
      .rule(theoryInstAndSimp(Options::TheoryInstSimp::ALL))
      .input(    clause({  tail(x) != tail(y), 
          head(x) != 0, 
          head(y) != 1, 
          tail(x) != nil(), 
          p(head(tail(x))), p(head(tail(y)))  }))
      .expected(exactly(
            clause({  p(head(tail(cons(0, nil())))), p(head(tail(cons(1,nil()))))  })
      ))
      .premiseRedundant(false)
    )

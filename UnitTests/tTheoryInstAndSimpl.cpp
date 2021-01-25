
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
                                                                                                              \
  DECL_FUNC(f, {Int}, Int)                                                                                    \
  DECL_PRED(p, {Int})                                                                                         \
  DECL_PRED(q, {Int})                                                                                         \
  DECL_PRED(r, {Int,Int})                                                                                     \
                                                                                                              \
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
      .input(    clause({ x == 1, x * y != 6, ~(0 < x), ~(x < y), r(x,y)  }))
      .expected(exactly(
            clause({ r(2,3)  })
      ))
      .premiseRedundant(false)
    )


TEST_GENERATION(test_01_1,
    Generation::TestCase()
      .rule(theoryInstAndSimp(Options::TheoryInstSimp::NEW))
      .input(    clause({ x == 1, x * y != 6, ~(0 < x), ~(x < y), r(x,y)  }))
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

TEST_GENERATION(test_02_1,
    Generation::TestCase()
      .rule(theoryInstAndSimp(Options::TheoryInstSimp::NEW))
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

#define LIST_ALPHA_SUGAR                                                                                      \
  DECL_DEFAULT_VARS                                                                                           \
  DECL_SORT(alpha)                                                                                            \
  DECL_LIST(alpha)                                                                                            \
  DECL_CONST(a, alpha)                                                                                        \
  DECL_PRED(p, {list})                                                                                        \

TEST_GENERATION_WITH_SUGAR(test_03,
    LIST_ALPHA_SUGAR,
    Generation::TestCase()
      .rule(theoryInstAndSimp(Options::TheoryInstSimp::ALL))
      .input(    clause({  cons(a, nil()) != cons(x, nil()), 
          p(x)  }))
      .expected(exactly(
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION_WITH_SUGAR(test_03_1,
    LIST_ALPHA_SUGAR,
    Generation::TestCase()
      .rule(theoryInstAndSimp(Options::TheoryInstSimp::NEW))
      .input(    clause({  cons(a, nil()) != cons(x, nil()), 
          p(x)  }))
      .expected(exactly(
      ))
      .premiseRedundant(false)
    )

#define RAT_SYNTAX_SUGAR                                                                                      \
    DECL_DEFAULT_VARS                                                                                         \
    NUMBER_SUGAR(Rat)                                                                                         \
    DECL_PRED(p, {Rat,Rat})                                                                                   \

TEST_GENERATION_WITH_SUGAR(test_04,
    RAT_SYNTAX_SUGAR,
    Generation::TestCase()
      .rule(theoryInstAndSimp(Options::TheoryInstSimp::NEW))
      .input(    clause({ x != 1, y != 4, p(x,y) }) )
      .expected(exactly())
      .premiseRedundant(false)
    )

TEST_GENERATION_WITH_SUGAR(test_05,
    RAT_SYNTAX_SUGAR,
    Generation::TestCase()
      .rule(theoryInstAndSimp(Options::TheoryInstSimp::NEW))
      .input(    clause({ x + y != 0, x != 7, p(x,y) }) )
      .expected(exactly(clause({p(7, -7)})))
      .premiseRedundant(false)
    )


TEST_GENERATION_WITH_SUGAR(test_06,
    RAT_SYNTAX_SUGAR,
    Generation::TestCase()
      .rule(theoryInstAndSimp(Options::TheoryInstSimp::NEW))
      .input(    clause({ x + y != 0 * z, x != 7, p(x,y) }) )
      .expected(exactly(clause({p(7, -7)})))
      .premiseRedundant(false)
    )

#define PAIR_SYNTAX_SUGAR                                                                                     \
  DECL_DEFAULT_VARS                                                                                           \
  NUMBER_SUGAR(Int)                                                                                           \
  DECL_SORT(Pair)                                                                                             \
                                                                                                              \
  DECL_FUNC(pair, { Int, Int },  Pair)                                                                        \
                                                                                                              \
  DECL_TERM_ALGEBRA(Pair, {pair})                                                                             \
  __ALLOW_UNUSED(                                                                                             \
    auto fst = pair.dtor(0);                                                                                  \
    auto snd = pair.dtor(1);                                                                                  \
  )                                                                                                           \

TEST_GENERATION_WITH_SUGAR(bug_01,
    PAIR_SYNTAX_SUGAR,
    Generation::TestCase()
      .rule(theoryInstAndSimp(Options::TheoryInstSimp::NEW))
      .input(    clause({ 0 != fst(pair(0,127)) }))
      .expected(exactly( clause({}) ))
      .premiseRedundant(true)
    )


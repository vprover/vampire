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
#include "Indexing/TermSharing.hpp"
#include "Inferences/IRC/TermFactoring.hpp"
#include "Inferences/InterpretedEvaluation.hpp"
#include "Kernel/Ordering.hpp"
#include "Inferences/PolynomialEvaluation.hpp"
#include "Inferences/Cancellation.hpp"

#include "Test/SyntaxSugar.hpp"
#include "Test/TestUtils.hpp"
#include "Lib/Coproduct.hpp"
#include "Test/SimplificationTester.hpp"
#include "Test/GenerationTester.hpp"
#include "Kernel/KBO.hpp"
#include "Indexing/TermSubstitutionTree.hpp"
#include "Inferences/PolynomialEvaluation.hpp"

using namespace std;
using namespace Kernel;
using namespace Inferences;
using namespace Test;
using namespace Indexing;
using namespace Inferences::IRC;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// TEST CASES 
/////////////////////////////////////

#define SUGAR(Num)                                                                                            \
  NUMBER_SUGAR(Num)                                                                                           \
  DECL_DEFAULT_VARS                                                                                           \
  DECL_VAR(x1, 1)                                                                                             \
  DECL_VAR(x2, 2)                                                                                             \
  DECL_VAR(x3, 3)                                                                                             \
  DECL_FUNC(f, {Num}, Num)                                                                                    \
  DECL_FUNC(g, {Num, Num}, Num)                                                                               \
  DECL_FUNC(h, {Num, Num, Num}, Num)                                                                          \
  DECL_CONST(a, Num)                                                                                          \
  DECL_CONST(b, Num)                                                                                          \
  DECL_CONST(c, Num)                                                                                          \
  DECL_PRED(p, {Num})                                                                                         \
  DECL_PRED(r, {Num,Num})                                                                                     \

#define MY_SYNTAX_SUGAR SUGAR(Rat)


TermFactoring testTermFactoring(
    Options::UnificationWithAbstraction uwa = Options::UnificationWithAbstraction::ONE_INTERP
    )
{ 
  return TermFactoring(testIrcState(uwa));
}

REGISTER_GEN_TESTER(Test::Generation::GenerationTester<TermFactoring>(testTermFactoring()))

/////////////////////////////////////////////////////////
// Basic tests
//////////////////////////////////////

TEST_GENERATION(basic01a,
    Generation::TestCase()
      .input   (  clause({selected( 3 * g(a, x) + 2 * g(y, b) > 0 ), p(x) }) )
      .expected(exactly(
          /* nothing because uninterpreted stuff is bigger */
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION(basic01b,
    Generation::TestCase()
      .input   (  clause({selected( 3 * g(a, x) + 2 * g(y, b) > 0 ), f(x)  == 1 }) )
      .expected(exactly(
            clause({ 5 * g(a,b) > 0, f(b) == 1  })
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION(basic02,
    Generation::TestCase()
      .input   (  clause({ selected( 1 * f(x) +  -1 * f(a) > 0 )  }) )
      .expected(exactly(
            clause({      num(0) > 0 }) 
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION(basic03,
    Generation::TestCase()
      .input   (  clause({ selected( 1 * f(x) +  -1 * f(y) > 0 )  }) )
      .expected(exactly(
            clause({      num(0) > 0 }) 
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION(basic04,
    Generation::TestCase()
      .rule(new TermFactoring(testTermFactoring(Shell::Options::UnificationWithAbstraction::OFF)))
      .input   (  clause({ selected(h(a, x, x1) + h(x, x, x2) + h(b, x, x3) > 0)  }) )
      .expected(exactly(
                  clause({ 2 * h(a, a, x) + h(b, a, y) > 0  }) 
                , clause({ 2 * h(b, b, y) + h(a, b, x) > 0  }) 
      ))
      .premiseRedundant(false)
    )

/////////////////////////////////////////////////////////
// UWA tests
//////////////////////////////////////

TEST_GENERATION(abstraction1,
    Generation::TestCase()
      .input   (  clause({ selected(-f(f(x) + g(a, c)) + f(f(y) + g(b, c)) > 0)   }))
      .expected(exactly(
            clause({ num(0) > 0, f(y) + g(b, c) != f(x) + g(a, c) })
      ))
      .premiseRedundant(false)
    )




/////////////////////////////////////////////////////////
// Bug fixes
//////////////////////////////////////

TEST_GENERATION(fix01,
    Generation::TestCase()
// 1 + f26(f34(f59,X0),X0) + f26(f34(f59,X1),X1) > 0 [theory normalization 1587]
// 2 * f26(f34(f59,X0),X0) + f26(f34(f59,X0),X0) > 0 [inequality factoring 2373]
      .input   (          clause({ selected(1 + f(x) + f(y) > 0)  })    )
      .expected(exactly(  clause({          1 +    2 * f(x) > 0   })   ))
      .premiseRedundant(false)
    )




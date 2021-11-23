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
#include "Inferences/IRC/LiteralFactoring.hpp"
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
  DECL_VAR(x0,0)                                                                                              \
  DECL_VAR(x1,1)                                                                                              \
  DECL_VAR(x2,2)                                                                                              \
  DECL_VAR(x3,3)                                                                                              \
  DECL_VAR(x4,4)                                                                                              \
  DECL_CONST(a, Num)                                                                                          \
  DECL_CONST(b, Num)                                                                                          \
  DECL_CONST(c, Num)                                                                                          \
  DECL_FUNC(f, {Num}, Num)                                                                                    \
  DECL_FUNC(g, {Num, Num}, Num)                                                                               \
  DECL_FUNC(g0, {Num, Num}, Num)                                                                              \
  DECL_FUNC(g1, {Num, Num}, Num)                                                                              \
  DECL_PRED(r, {Num,Num})                                                                                     \

#define MY_SYNTAX_SUGAR SUGAR(Rat)


LiteralFactoring testLiteralFactoring(
    Options::UnificationWithAbstraction uwa = Options::UnificationWithAbstraction::IRC1
    )
{ return LiteralFactoring(testIrcState(uwa)); }

REGISTER_GEN_TESTER(Test::Generation::GenerationTester<LiteralFactoring>(testLiteralFactoring()))

/////////////////////////////////////////////////////////
// Basic tests
//////////////////////////////////////

// TODO write test for maximality side conditions

TEST_GENERATION(basic01,
    Generation::SymmetricTest()
      .inputs  ({  clause({selected( 3 * f(x) + x > 0 ), selected(4 * f(y) + x > 0)   }) })
      .expected(exactly(
            clause({          3 * f(x) + x > 0 , 4 * x  + -3 * x != 0            })
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION(basic02,
    Generation::SymmetricTest()
      .inputs  ({  clause({selected(f(a) + b > 0), selected(f(x) + x > 0)   }) })
      .expected(exactly(
            clause({          f(a) + b > 0 , b - a != 0            })
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION(basic03,
    Generation::SymmetricTest()
      .inputs  ({  clause({selected(  f(a) > 0)  , selected(  f(a) > 0)  }) })
      .expected(exactly(
            clause({  f(a) > 0, num(0) != 0  })
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION(basic04,
    Generation::SymmetricTest()
      .inputs  ({  clause({selected(  -f(a) > 0)  , selected(  f(a) > 0)  }) })
      .expected(exactly(
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION(uwa1,
    Generation::SymmetricTest()
      .inputs  ({  clause({selected(  f(a + b + x) > 0)  , selected(f(y + a) > 0)  }) })
      .expected(exactly(
            clause({  f(a + b + x) > 0, num(0) != 0, a + b + x != y + a  })
      ))
      .premiseRedundant(false)
    )

/////////////////////////////////////////////////////////
// MISC
//////////////////////////////////////

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
#include "Inferences/InequalityResolutionCalculus/LiteralFactoring.hpp"
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
using namespace Inferences::InequalityResolutionCalculus;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// TEST CASES 
/////////////////////////////////////

#define SUGAR(Num)                                                                                            \
  NUMBER_SUGAR(Num)                                                                                           \
  DECL_DEFAULT_VARS                                                                                           \
  DECL_FUNC(f, {Num}, Num)                                                                                    \
  DECL_FUNC(g, {Num, Num}, Num)                                                                               \
  DECL_CONST(a, Num)                                                                                          \
  DECL_CONST(b, Num)                                                                                          \
  DECL_CONST(c, Num)                                                                                          \
  DECL_PRED(r, {Num,Num})                                                                                     \

#define MY_SYNTAX_SUGAR SUGAR(Rat)


inline Stack<Indexing::Index*> indices() 
{ 
  auto uwa = Options::UnificationWithAbstraction::ONE_INTERP;
  return {
    new InequalityResolutionIndex(new TermSubstitutionTree(uwa, true))
  };
}

LiteralFactoring testLiteralFactoring(
    Options::UnificationWithAbstraction uwa = Options::UnificationWithAbstraction::ONE_INTERP
    )
{ return LiteralFactoring(testIrcState(uwa)); }

REGISTER_GEN_TESTER(Test::Generation::GenerationTester<LiteralFactoring>(testLiteralFactoring()))

/////////////////////////////////////////////////////////
// Basic tests
//////////////////////////////////////

TEST_GENERATION(basic01,
    Generation::TestCase()
      .indices(indices())
      .input   (  clause({selected( 3 * f(x) + x > 0 ), selected(4 * f(y) + x > 0)   }) )
      .expected(exactly(
            clause({          3 * f(x) + x > 0 , 4 * x - 3 * x != 0            })
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION(basic02,
    Generation::TestCase()
      .indices(indices())
      .input   (  clause({selected(f(a) + b > 0 ), selected(f(x) + x > 0)   }) )
      .expected(exactly(
            clause({          f(a) + b > 0 , a - b != 0            })
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION(basic03,
    Generation::TestCase()
      .indices(indices())
      .input   (  clause({selected(  f(a) > 0)  , selected(  f(a) > 0)  }) )
      .expected(exactly(
            clause({  f(a) > 0, num(0) != 0  })
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION(uwa1,
    Generation::TestCase()
      .indices(indices())
      .input   (  clause({selected(  f(a + b + y) > 0)  , selected(f(x + a) > 0)  }) )
      .expected(exactly(
            clause({  f(a + b + y) > 0, num(0) != 0, a + b + y != x + a  })
      ))
      .premiseRedundant(false)
    )


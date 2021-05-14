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
#include "Inferences/IRC/VariableElimination.hpp"
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
  DECL_FUNC(f, {Num}, Num)                                                                                    \
  DECL_FUNC(g, {Num, Num}, Num)                                                                               \
  DECL_CONST(a, Num)                                                                                          \
  DECL_CONST(b, Num)                                                                                          \
  DECL_CONST(c, Num)                                                                                          \
  DECL_PRED(R, {Num,Num})                                                                                     \
  DECL_PRED(P, {Num})                                                                                         \

#define MY_SYNTAX_SUGAR SUGAR(Rat)


VariableElimination testVariableElimination(
    Options::UnificationWithAbstraction uwa = Options::UnificationWithAbstraction::ONE_INTERP
    )
{ 
  return VariableElimination(testIrcState(uwa));
}



REGISTER_GEN_TESTER(Test::Generation::GenerationTester<VariableElimination>(testVariableElimination()))

/////////////////////////////////////////////////////////
// Basic tests
//////////////////////////////////////

TEST_GENERATION(basic01,
    Generation::TestCase()
      .input  (  clause({x + a > 0, x + b > 0 }) )
      .expected(exactly(
            clause({})
      ))
      .premiseRedundant(true)
    )
TEST_GENERATION(basic02,
    Generation::TestCase()
      .input  (  clause({x + a > 0, - x + b > 0 }) )
      .expected(exactly(
            clause({ a + b > 0 })
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(basic03,
    Generation::TestCase()
      .input  (  clause({x + a > 0, - x + b > 0, f(y) + c > 0 }) )
      .expected(exactly(
        clause({a + b > 0, f(y) + c > 0 }) 
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(basic04,
    Generation::TestCase()
      .input  (  clause({ x + a > 0, -x + b >= 0, x + c >= 0 }) )
      .expected(exactly(
            clause({ a + b >= 0, b + c >= 0 })
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(basic05,
    Generation::TestCase()
      .input  (  clause({ x + a > 0, -x + b >= 0, - x - c >= 0 }) )
      .expected(exactly(
            clause({ a + b >= 0, a - c >= 0 })
      ))
      .premiseRedundant(true)
    )


/////////////////////////////////////////////////////////
// Only use unshielded variables
//////////////////////////////////////

TEST_GENERATION(shielded01,
    Generation::TestCase()
      .input  (  clause({x + a > 0, - x + b > 0, f(x) + c > 0 }) )
      .expected(exactly())
      .premiseRedundant(false)
    )

TEST_GENERATION(shielded02,
    Generation::TestCase()
      .input  (  clause({ x + a > 0, - x + b > 0, P(x) }) )
      .expected(exactly())
      .premiseRedundant(false)
    )

/////////////////////////////////////////////////////////
// EQ TEST
//////////////////////////////////////

TEST_GENERATION(eq01a,
    Generation::TestCase()
      .input  (  clause({ x + a >= 0, x - b == 0, P(y) }) )
      .expected(exactly(
            clause({ a + b >= 0, P(y) }),
            clause({ P(y) }) // TODO can we detect redundancies of that kind?
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(eq01b,
    Generation::TestCase()
      .input  (  clause({ x + a >= 0, - x + b == 0, P(y) }) )
      .expected(exactly(
            clause({ a + b >= 0, P(y) }),
            clause({ P(y) }) // TODO can we detect redundancies of that kind?
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(eq02a,
    Generation::TestCase()
      .input  (  clause({ x + a > 0, x - b == 0, P(y) }) )
      .expected(exactly(
            clause({ a + b >= 0, P(y) }),
            clause({ P(y) }) // TODO can we detect redundancies of that kind?
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(eq02b,
    Generation::TestCase()
      .input  (  clause({ x + a > 0, - x + b == 0, P(y) }) )
      .expected(exactly(
            clause({ a + b >= 0, P(y) }),
            clause({ P(y) }) // TODO can we detect redundancies of that kind?
      ))
      .premiseRedundant(true)
    )


TEST_GENERATION(eq03a,
    Generation::TestCase()
      .input  (  clause({ -x + a > 0, x - b == 0, P(y) }) )
      .expected(exactly(
            clause({ P(y) }), // TODO can we detect redundancies of that kind?
            clause({ a - b >= 0, P(y) })
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(eq03b,
    Generation::TestCase()
      .input  (  clause({ -x + a > 0, - x + b == 0, P(y) }) )
      .expected(exactly(
            clause({ P(y) }), // TODO can we detect redundancies of that kind?
            clause({ a - b >= 0, P(y) })
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(eq04a,
    Generation::TestCase()
      .input  (  clause({ x + a > 0, -x + b >= 0, - x - c == 0 }) )
      .expected(exactly(
            clause({ a + b >= 0, a - c >= 0 }),
            clause({ a + b >= 0, b + c >= 0 })
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(eq04b,
    Generation::TestCase()
      .input  (  clause({ x + a > 0, -x + b >= 0, x + c == 0 }) )
      .expected(exactly(
            clause({ a + b >= 0, a - c >= 0 }),
            clause({ a + b >= 0, b + c >= 0 })
      ))
      .premiseRedundant(true)
    )

/////////////////////////////////////////////////////////
// NOT EQ TEST
//////////////////////////////////////

  // TODO

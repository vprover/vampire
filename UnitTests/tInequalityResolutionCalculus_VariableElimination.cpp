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
#include "Inferences/InequalityResolutionCalculus/VariableElimination.hpp"
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
  auto& kbo = *new KBO(KBO::testKBO());
  // auto uwa = env.options->unificationWithAbstraction();
  auto uwa = Options::UnificationWithAbstraction::ONE_INTERP;
  return {
    new InequalityResolutionIndex(
        new TermSubstitutionTree(uwa, true), kbo,
        InequalityNormalizer(PolynomialEvaluation(kbo)))
  };
}

VariableElimination testVariableElimination(
    Options::UnificationWithAbstraction uwa = Options::UnificationWithAbstraction::ONE_INTERP
    )
{ 
  auto& kbo = *new KBO(KBO::testKBO());
  return VariableElimination(*new InequalityNormalizer(kbo), &kbo, uwa);
}



REGISTER_GEN_TESTER(Test::Generation::GenerationTester<VariableElimination>(testVariableElimination()))

/////////////////////////////////////////////////////////
// Basic tests
//////////////////////////////////////

TEST_GENERATION(basic01,
    Generation::TestCase()
      .indices(indices())
      .input  (  clause({x + a > 0, x + b > 0 }) )
      .expected(exactly(
            clause({})
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(basic02,
    Generation::TestCase()
      .indices(indices())
      .input  (  clause({x + a > 0, - x + b > 0 }) )
      .expected(exactly(
            clause({ a + b > 0 })
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(basic03,
    Generation::TestCase()
      .indices(indices())
      .input  (  clause({x + a > 0, - x + b > 0, f(x) + c > 0 }) )
      .expected(exactly(
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(basic04,
    Generation::TestCase()
      .indices(indices())
      .input  (  clause({x + a > 0, - x + b > 0, f(y) + c > 0 }) )
      .expected(exactly(
        clause({a + b > 0, f(y) + c > 0 }) 
      ))
      .premiseRedundant(true)
    )

// TODO more test cases

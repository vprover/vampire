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
#include "Test/GenerationTester.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Inferences/PolynomialMultiplication.hpp"


using namespace std;
using namespace Kernel;
using namespace Inferences;
using namespace Test;

// ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// ////// TEST UNIT INITIALIZATION
// /////////////////////////////////////

#define MY_SYNTAX_SUGAR                                                                                       \
  NUMBER_SUGAR(Real)                                                                                          \
  DECL_DEFAULT_VARS                                                                                           \
  DECL_CONST(a, Real)                                                                                         \
  DECL_CONST(b, Real)                                                                                         \
  DECL_CONST(c, Real)                                                                                         \
  DECL_FUNC(f, {Real}, Real)                                                                                  \
  DECL_PRED(p, {Real})                                                                                        \
  DECL_PRED(q, {Real})                                                                                        \


REGISTER_GEN_TESTER(Test::Generation::GenerationTester<PolynomialMultiplication>)

TEST_GENERATION(test_01,
    Generation::AsymmetricCase()
      .input(            clause({  p(  (y + x) * (a + x)  )  })   )
      .expected(exactly( clause({  p(x*x + x*a + x*y + a*y)  })  ))
      .premiseRedundant(false)
    )

// TODO write more tests

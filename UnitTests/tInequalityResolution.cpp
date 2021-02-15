/*
 * File tInequalityResolution.cpp.
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
#include "Inferences/InequalityResolution.hpp"
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

using namespace std;
using namespace Kernel;
using namespace Inferences;
using namespace Test;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// TEST CASES 
/////////////////////////////////////

#define MY_SYNTAX_SUGAR                                                                                       \
  NUMBER_SUGAR(Rat)                                                                                           \
  DECL_DEFAULT_VARS                                                                                           \
  DECL_FUNC(f, {Rat}, Rat)                                                                                    \
  DECL_CONST(a, Rat)                                                                                          \
  DECL_CONST(b, Rat)                                                                                          \


REGISTER_GEN_TESTER(Test::Generation::GenerationTester<InequalityResolution>)

TEST_GENERATION(test01,
    Generation::TestCase()
      .input   (  clause({  f(x) > 0, x == 7  }) )
      .context ({ clause({ -f(x) > 0 }) })
      .expected(exactly(
            clause({  x == 7  })
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION(test02,
    Generation::TestCase()
      .input   (  clause({  f(a) > 0  }) )
      .context ({ clause({ a + f(a) > 0 }) })
      .expected(exactly(
            clause({  -a > 0  })
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION(test03,
    Generation::TestCase()
      .input   (  clause({ -a + f(a) > 0 }) )
      .context ({ clause({  a + f(a) > 0 }) })
      .expected(exactly(
            clause({  -2 * a > 0  })
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION(test04,
    Generation::TestCase()
      .input   (  clause({ -a + f(x) > 0 }) )
      .context ({ clause({  a + f(a) > 0 }) })
      .expected(exactly(
            clause({  -2 * a > 0  })
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION(test05,
    Generation::TestCase()
      .input   (  clause({ f(x) > 0 }) )
      .context ({ clause({ f(y) + f(a) > 0 }) })
      .expected(exactly(
            clause({  -f(a) > 0 }),
            clause({  -f(x) > 0 })
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION(test06,
    Generation::TestCase()
      .input   (  clause({ 6 * f(x) + b > 0 })  )
      .context ({ clause({ 4 * f(y) + a > 0 }) })
      .expected(exactly(
            clause({  -2 * b  + 3 * a  > 0 })
      ))
      .premiseRedundant(false)
    )

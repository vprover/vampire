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
#include "Inferences/ALASCA/SubtermFactoring.hpp"
#include "Lib/STL.hpp"
#include "Inferences/InterpretedEvaluation.hpp"
#include "Kernel/Ordering.hpp"
#include "Inferences/PolynomialEvaluation.hpp"
#include "Inferences/Cancellation.hpp"

#include "Test/SyntaxSugar.hpp"
#include "Test/TestUtils.hpp"
#include "Lib/Coproduct.hpp"
#include "Test/AlascaTestUtils.hpp"
#include "Test/GenerationTester.hpp"
#include "Kernel/KBO.hpp"
#include "Indexing/TermSubstitutionTree.hpp"
#include "Inferences/PolynomialEvaluation.hpp"

using namespace std;
using namespace Kernel;
using namespace Inferences;
using namespace Test;
using namespace Indexing;
using namespace Inferences::ALASCA;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// TEST CASES 
/////////////////////////////////////

#define SUGAR(Num)                                                                        \
  NUMBER_SUGAR(Num)                                                                       \
  DECL_DEFAULT_VARS                                                                       \
  DECL_VAR(x0, 0)                                                                         \
  DECL_VAR(x1, 1)                                                                         \
  DECL_VAR(x2, 2)                                                                         \
  DECL_VAR(x3, 3)                                                                         \
  DECL_VAR(x4, 4)                                                                         \
  DECL_FUNC(f, {Num}, Num)                                                                \
  DECL_FUNC(g, {Num, Num}, Num)                                                           \
  DECL_CONST(a, Num)                                                                      \
  DECL_CONST(b, Num)                                                                      \
  DECL_CONST(c, Num)                                                                      \
  DECL_PRED(p, {Num})                                                                     \
  DECL_PRED(r, {Num,Num})                                                                 \

#define MY_SYNTAX_SUGAR SUGAR(Rat)


REGISTER_GEN_TESTER(AlascaGenerationTester<SubtermFactoring>())

/////////////////////////////////////////////////////////
// Basic tests
//////////////////////////////////////

TEST_GENERATION(basic01,
    Generation::SymmetricTest()
      .inputs  ({  clause({ f(f(x) - f(y)) + f(x) > 0  }) })
      .expected(exactly(
          clause({ f(0) + f(x) > 0 })
      )))

TEST_GENERATION(basic02,
    Generation::SymmetricTest()
      .inputs  ({  clause({ f(f(x) - f(0)) + f(x) > 0  }) })
      .expected(exactly(
          clause({ f(0) + f(0) > 0 })
      )))

TEST_GENERATION(basic03,
    Generation::SymmetricTest()
      .inputs  ({  clause({ r(f(x) - f(0), x)  }) })
      .expected(exactly(
          clause({ r(0, 0) })
      )))

TEST_GENERATION(basic04,
    Generation::SymmetricTest()
      .inputs  ({  clause({ p(x + f(y))   }) })
      .expected(exactly(
          /* nothing, this is done by abstraction */
      )))


TEST_GENERATION(basic05,
    Generation::SymmetricTest()
      .inputs  ({  clause({ f(f(f(x) + f(y)) - f(0)) + f(x) > 0  }) })
      .expected(exactly(
          clause({ f(f(2 * f(x)) - f(0)) + f(x) > 0 })
      )))


  // TODO make sure we don't generate duplicates somehow
TEST_GENERATION(misc_01,
    Generation::SymmetricTest()
      .inputs  ({        clause({  f(x) + f(y) + f(z) == floor(f(x) + f(y) + f(z))  }) })
      .expected(exactly( 
            clause({  f(x) + 2 * f(y) == floor(f(x) + 2 * f(y))  }) 
          , clause({  f(x) + 2 * f(y) == floor(f(x) + 2 * f(y))  }) 
          , clause({  f(x) + 2 * f(y) == floor(f(x) + 2 * f(y))  }) 
          )))

TEST_GENERATION(misc_02,
    Generation::SymmetricTest()
      .inputs  ({
            clause({  f(x) + 2 * f(y) == floor(f(x) + 2 * f(y))  }) 
        })
      .expected(exactly( 
            clause({  3 * f(x) == floor(3 * f(x))  }) 
          )))

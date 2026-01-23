/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Inferences/ALASCA/Normalization.hpp"
#include "Test/SyntaxSugar.hpp"

#include "Test/SyntaxSugar.hpp"
#include "Test/GenerationTester.hpp"
#include "Test/AlascaTestUtils.hpp"

using namespace std;
using namespace Kernel;
using namespace Inferences;
using namespace Test;
using namespace Indexing;
using namespace Inferences::ALASCA;
#define INT_TESTS 0

///////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// TEST CASES 
/////////////////////////////////////

namespace {

#define SUGAR(Num)                                                                        \
  NUMBER_SUGAR(Num)                                                                       \
                                                                                          \
  DECL_DEFAULT_VARS                                                                       \
                                                                                          \
  DECL_FUNC(f, {Num}, Num)                                                                \
  DECL_FUNC(f2, {Num,Num}, Num)                                                           \
  DECL_FUNC(g, {Num}, Num)                                                                \
  DECL_FUNC(h, {Num}, Num)                                                                \
                                                                                          \
  DECL_CONST(a, Num)                                                                      \
  DECL_CONST(b, Num)                                                                      \
  DECL_CONST(c, Num)                                                                      \
                                                                                          \
  DECL_PRED(p, {Num})                                                                     \
  DECL_PRED(r, {Num,Num})                                                                 \
                                                                                          \
  auto isInteger = [&](auto t) { return t == floor(t); };                                 \


#define MY_GEN_RULE     AlascaSimplRule<ToSgi<FloorElimination>>
#define MY_GEN_TESTER   AlascaGenerationTester
#define MY_SYNTAX_SUGAR SUGAR(Real)

/////////////////////////////////////////////////////////
// Basic tests
//////////////////////////////////////

TEST_GENERATION(basic_success01,
    alascaSymmetricTest()
      .inputs  ({ clause({ floor(a) == frac(1,2)  }) })
      .premiseRedundant(true)
      .expected(exactly(
            clause({  })
      ))
    )

TEST_GENERATION(basic_success02,
    alascaSymmetricTest()
      .inputs  ({ clause({ floor(a) == frac(-1,2)  }) })
      .premiseRedundant(true)
      .expected(exactly(
            clause({  })
      ))
    )

TEST_GENERATION(basic_success03,
    alascaSymmetricTest()
      .inputs  ({ clause({ 5 * floor(x) == num(4)  }) })
      .premiseRedundant(true)
      .expected(exactly(
            clause({  })
      ))
    )

TEST_GENERATION(basic_success04,
    alascaSymmetricTest()
      .inputs  ({ clause({ p(x), 5 * floor(x) == num(4)  }) })
      .premiseRedundant(true)
      .expected(exactly(
            clause({ p(x) })
      ))
    )

TEST_GENERATION(basic_fail01,
    alascaSymmetricTest()
      .inputs  ({ clause({ floor(a) == frac(1,1)  }) })
      .premiseRedundant(false)
      .expected(exactly(
            /* nothing */
      ))
    )

TEST_GENERATION(basic_fail02,
    alascaSymmetricTest()
      .inputs  ({ clause({ floor(a) == frac(1,1) + b  }) })
      .premiseRedundant(false)
      .expected(exactly(
            /* nothing */
      ))
    )

TEST_GENERATION(basic_fail03,
    alascaSymmetricTest()
      .inputs  ({ clause({ 2 *floor(a) == num(4)  }) })
      .premiseRedundant(false)
      .expected(exactly(
            /* nothing */
      ))
    )

TEST_GENERATION(basic_fail04,
    alascaSymmetricTest()
      .inputs  ({ clause({ floor(a) + floor(b) == frac(1,1)  }) })
      .premiseRedundant(false)
      .expected(exactly(
            /* nothing */
      ))
    )

}
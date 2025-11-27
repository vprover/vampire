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
#include "Inferences/ALASCA/Abstractions.hpp"
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


#define MY_SYNTAX_SUGAR SUGAR(Real)

#define UWA_MODE Options::UnificationWithAbstraction::ALASCA_MAIN

inline auto testAbstraction(Options::UnificationWithAbstraction uwa)
{ 
  auto s = testAlascaState(uwa);
  return alascaSimplRule(s,toSgi(Abstraction<RealTraits>(s)), Normalization(s));
}



REGISTER_GEN_TESTER(AlascaGenerationTester<ToSgi<Abstraction<RealTraits>>>(testAbstraction(UWA_MODE)))

/////////////////////////////////////////////////////////
// Basic tests
//////////////////////////////////////

#define UNSTABILITY_ABSTRACTION 0

#if UNSTABILITY_ABSTRACTION 
TEST_GENERATION(stabilizing_1,
    Generation::SymmetricTest()
      .inputs  ({ clause({ 0 != x + f(f2(x,y) - f2(x, a))  }) })
      .premiseRedundant(true)
      .expected(exactly(
            clause({  0 != -z + f2(x,y) - f2(x, a),  0 != x + f(z) })
      ))
    )

TEST_GENERATION(stabilizing_2,
    Generation::SymmetricTest()
      .inputs  ({ clause({ x + a > 0, 0 != f(f2(x,y) - f2(x, a))  }) })
      .premiseRedundant(true)
      .expected(exactly(
            clause({  0 != -z + f2(x,y) - f2(x, a),  x + a > 0, 0 != f(z) })
      ))
    )

TEST_GENERATION(stabilizing_3,
    Generation::SymmetricTest()
      .inputs  ({ clause({ 0 != x + f(f(f2(x,y) - f2(x, a)) - f(x))  }) })
      .premiseRedundant(true)
      .expected(exactly(
            clause({ 0 != -z + f(f2(x,y) - f2(x, a)) - f(x), 0 != x + f(z)  })
      ))
    )
#endif // UNSTABILITY_ABSTRACTION

TEST_GENERATION(coherence_1,
    Generation::SymmetricTest()
      .inputs  ({ clause({ p(floor(y))  }) })
      .premiseRedundant(true)
      .expected(exactly(
            clause({  0 != -z + floor(y),  p(z) })
      ))
    )

TEST_GENERATION(coherence_2,
    Generation::SymmetricTest()
      .inputs  ({ clause({ p(floor(frac(1,2) * floor(y)))  }) })
      .premiseRedundant(true)
      .expected(exactly(
            clause({  0 != -z + floor(frac(1,2) * floor(y)),  p(z) })
      ))
    )

TEST_GENERATION(coherence_3,
    Generation::SymmetricTest()
      .inputs  ({ clause({ p(floor(2 * y + a) + b)  }) })
      .premiseRedundant(true)
      .expected(exactly(
            clause({  0 != -z + floor(2 * y + a),  p(z + b) })
      ))
    )

TEST_GENERATION(coherence_4,
    Generation::SymmetricTest()
      .inputs  ({ clause({ p(2 * x + a + b)  }) })
      .premiseRedundant(false)
      .expected(exactly(
          /* nothing */
      ))
    )

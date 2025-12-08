/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Shell/Options.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Inferences/ALASCA/IntegerFourierMotzkin.hpp"

#include "Test/SyntaxSugar.hpp"
#include "Test/GenerationTester.hpp"
#include "Test/AlascaTestUtils.hpp"

using namespace std;
using namespace Kernel;
using namespace Inferences;
using namespace Test;
using namespace Indexing;
using namespace Inferences::ALASCA;
// TODO tests for Rationals

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
  DECL_VAR(x5, 5)                                                                         \
  DECL_VAR(x6, 6)                                                                         \
  DECL_VAR(x7, 7)                                                                         \
  DECL_VAR(x8, 8)                                                                         \
  DECL_VAR(x9, 9)                                                                         \
  DECL_VAR(x10, 10)                                                                       \
  DECL_VAR(x11, 11)                                                                       \
  DECL_VAR(x12, 12)                                                                       \
  DECL_VAR(x13, 13)                                                                       \
  DECL_VAR(x14, 14)                                                                       \
  DECL_VAR(x15, 15)                                                                       \
  DECL_VAR(x16, 16)                                                                       \
  DECL_VAR(x17, 17)                                                                       \
  DECL_VAR(x18, 18)                                                                       \
  DECL_VAR(x19, 19)                                                                       \
  DECL_VAR(x20, 20)                                                                       \
  DECL_VAR(x21, 21)                                                                       \
  DECL_VAR(x22, 22)                                                                       \
  DECL_VAR(x23, 23)                                                                       \
  DECL_VAR(x24, 24)                                                                       \
  DECL_VAR(x25, 25)                                                                       \
  DECL_VAR(x26, 26)                                                                       \
  DECL_VAR(x27, 27)                                                                       \
  DECL_VAR(x28, 28)                                                                       \
  DECL_VAR(x29, 29)                                                                       \
  DECL_FUNC(f, {Num}, Num)                                                                \
  DECL_FUNC(f3, {Num,Num,Num}, Num)                                                                \
  DECL_FUNC(g, {Num, Num}, Num)                                                           \
  DECL_CONST(a, Num)                                                                      \
  DECL_CONST(a0, Num)                                                                     \
  DECL_CONST(a1, Num)                                                                     \
  DECL_CONST(a2, Num)                                                                     \
  DECL_CONST(a3, Num)                                                                     \
  DECL_CONST(b, Num)                                                                      \
  DECL_CONST(c, Num)                                                                      \
  DECL_PRED(r, {Num,Num})                                                                 \
  DECL_SORT(srt)                                                                          \
  DECL_CONST(au, srt)                                                                     \
  DECL_CONST(bu, srt)                                                                     \
  DECL_FUNC(fu, {Num}, srt)                                                               \
  DECL_FUNC(fn, {srt}, Num)                                                               \
  DECL_CONST(delta, Num)                                                                  \
  DECL_FUNC(gg, {Num}, Num)                                                               \
  DECL_FUNC(ff, {Num}, Num)                                                               \
  DECL_FUNC(ab, {Num}, Num)                                                               \
  DECL_FUNC(skx, {Num}, Num)                                                              \

#define MY_SYNTAX_SUGAR SUGAR(Real)

auto idxIntegerFourierMotzkin() { 
  return Generation::TestIndices{
    [=](const SaturationAlgorithm&) { return new AlascaIndex<IntegerFourierMotzkin<RealTraits>::Premise0>(); },
    [=](const SaturationAlgorithm&) { return new AlascaIndex<IntegerFourierMotzkin<RealTraits>::Premise1>(); },
    [=](const SaturationAlgorithm&) { return new AlascaIndex<IntegerFourierMotzkin<RealTraits>::Premise2>(); },
  }; 
}

auto testIntegerFourierMotzkin(
   Options::UnificationWithAbstraction uwa = Options::UnificationWithAbstraction::ALASCA_MAIN
    ) 
{ 
  auto s = testAlascaState(uwa);
  return alascaSimplRule(s, IntegerFourierMotzkin<RealTraits>(s), s); 
}

REGISTER_GEN_TESTER(AlascaGenerationTester<IntegerFourierMotzkin<RealTraits>>(testIntegerFourierMotzkin()))

/////////////////////////////////////////////////////////
// Basic tests
//////////////////////////////////////

#define isInt(t) floor(t) == t

TEST_GENERATION(basic01,
    Generation::SymmetricTest()
      .indices(idxIntegerFourierMotzkin())
      .inputs  ({ clause({ f3(a,b,c)  + a  > 0   }) 
               ,  clause({ -f3(a,b,c) + b > 0   }) 
               ,  clause({ isInt(f3(a,b,c)) }) })
      .expected(exactly(
            clause({  ceil(a) + ceil(b) - 2 > 0, f3(a,b,c) + ceil(a) == 1  })
      ))
    )

TEST_GENERATION(basic02,
    Generation::SymmetricTest()
      .indices(idxIntegerFourierMotzkin())
      .inputs  ({ clause({ f3(a,b,c)  + a  > 0   }) 
               ,  clause({ -f3(a,b,c) + b > 0   }) 
               ,  clause({ isInt(b) }) })
      .expected(exactly(
          /* nothing */
      ))
    )

TEST_GENERATION(basic03,
    Generation::SymmetricTest()
      .indices(idxIntegerFourierMotzkin())
      .inputs  ({ clause({ f3(a,b,c)  + a  > 0   }) 
               ,  clause({ -f3(a,b,c) + b > 0   }) 
               ,  clause({ f3(a,b,c) == floor(f(f3(a,b,c))) }) })
      .expected(exactly(
            clause({  ceil(a) + ceil(b) - 2 > 0, f3(a,b,c) + ceil(a) == 1  })
      ))
    )

TEST_GENERATION(basic04,
    Generation::SymmetricTest()
      .indices(idxIntegerFourierMotzkin())
      .inputs  ({ clause({ f3(a,b,c)  + a  > 0   }) 
               ,  clause({ -f3(a,b,c) + b > 0   }) 
               ,  clause({ isInt(2 * f3(a,b,c)) }) })
      .expected(exactly(
            clause({  ceil(2 * a) + ceil(2 * b) - 2 > 0, 2 * f3(a,b,c) + ceil(2 * a) == 1  })
      ))
    )

TEST_GENERATION(basic05,
    Generation::SymmetricTest()
      .indices(idxIntegerFourierMotzkin())
      .inputs  ({ clause({ f3(a,b,c)  + a  > 0   }) 
               ,  clause({ -f3(a,b,c) + b > 0   }) 
               ,  clause({ isInt(f3(a,b,c) / 2) }) })
      .expected(exactly(
            clause({  ceil(a / 2) + ceil(b / 2) - 2 > 0, f3(a,b,c) / 2 + ceil(a / 2) == 1  })
      ))
    )

TEST_GENERATION(basic06,
    Generation::SymmetricTest()
      .indices(idxIntegerFourierMotzkin())
      .inputs  ({ clause({ f3(a,b,c)  + a  > 0   }) 
               ,  clause({ -f3(a,b,c) + b > 0   }) 
               ,  clause({ isInt(f3(a,b,c) / 2 + frac(1,2)) }) })
      .expected(exactly(
            clause({  ceil(a / 2 - frac(1,2)) + ceil(b / 2 + frac(1,2)) - 2 > 0, f3(a,b,c) / 2 + frac(1,2) + ceil(a / 2 - frac(1,2)) == 1  })
      ))
    )

TEST_GENERATION(basic07,
    Generation::SymmetricTest()
      .indices(idxIntegerFourierMotzkin())
      .inputs  ({ clause({ f3(a,b,c)  + a  > 0   }) 
               ,  clause({ -f3(a,b,c) + b > 0   }) 
               ,  clause({ isInt(f3(a,b,c) / 2 + c) }) })
      .expected(exactly(
            clause({  ceil(a / 2 - c) + ceil(b / 2 + c) - 2 > 0, f3(a,b,c) / 2 + c + ceil(a / 2 - c) == 1  })
      ))
    )


TEST_GENERATION(bug01,
    Generation::SymmetricTest()
      .indices(idxIntegerFourierMotzkin())
      .inputs  ({ clause({ b  + a  > 0   }) 
               ,  clause({ -b - a > 0   }) 
               ,  clause({ floor(c) == -a - b }) })
      .expected(exactly(
            clause({               a + b == 1 })
      ))
    )

TEST_GENERATION(bug02,
    Generation::SymmetricTest()
      .indices(idxIntegerFourierMotzkin())
      .inputs  ({ clause({ b  + a >= 0   }) 
               ,  clause({ -b - a >= 0   }) 
               ,  clause({ floor(c) == -a - b }) })
      .expected(exactly(

      ))
    )


TEST_GENERATION(bug03,
    Generation::SymmetricTest()
      .indices(idxIntegerFourierMotzkin())
      .inputs  ({ clause({ f3(a, y, z)  + a > 0   }) 
               ,  clause({ -f3(x, b, z) - a > 0   }) 
               ,  clause({ floor(-a - f3(x, y, c)) == -a - f3(x, y, c) }) })
      .expected(exactly(
          clause({ 0 == a + -1 + f3(a,b,c) })
      ))
    )


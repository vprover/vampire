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
#include "Inferences/ALASCA/VIRAS.hpp"
#include "Inferences/ALASCA/VirasInterfacing.hpp"

#include "Test/SyntaxSugar.hpp"
#include "Test/GenerationTester.hpp"
#include "Test/AlascaTestUtils.hpp"

#include <viras.h>
#include <viras/test.h>

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
  DECL_FUNC(f, {Num}, Num)                                                                \
  DECL_FUNC(g, {Num}, Num)                                                                \
  DECL_FUNC(f2, {Num, Num}, Num)                                                          \
  DECL_CONST(a, Num)                                                                      \
  DECL_CONST(b, Num)                                                                      \
  DECL_CONST(c, Num)                                                                      \
  DECL_CONST(d, Num)                                                                      \
  DECL_CONST(e, Num)                                                                      \
  DECL_PRED(R, {Num,Num})                                                                 \
  DECL_PRED(P, {Num})                                                                     \

#define MY_SYNTAX_SUGAR SUGAR(Real)

REGISTER_GEN_TESTER(AlascaGenerationTester<VirasQuantifierElimination>())

/////////////////////////////////////////////////////////
// Basic tests
//////////////////////////////////////

TEST_GENERATION(ported_lra_test_basic01,
    Generation::SymmetricTest()
      .inputs ({  clause({x + a > 0, x + b > 0 }) })
      .expected(exactly(
            clause({})
      ))
      .premiseRedundant(true)
    )
TEST_GENERATION(ported_lra_test_basic02,
    Generation::SymmetricTest()
      .inputs ({  clause({x + a > 0, - x + b > 0 }) })
      .expected(exactly(
            clause({ a + b > 0 })
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(ported_lra_test_basic03,
    Generation::SymmetricTest()
      .inputs ({  clause({x + a > 0, - x + b > 0, f(y) + c > 0 }) })
      .expected(exactly(
        clause({a + b > 0, f(y) + c > 0 }) 
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(ported_lra_test_basic04,
    Generation::SymmetricTest()
      .inputs ({  clause({ x + a > 0, -x + b >= 0, x + c >= 0 }) })
      .expected(exactly(
            clause({ a + b >= 0, b + c >= 0 })
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(ported_lra_test_basic05_pos,
    Generation::SymmetricTest()
      .inputs ({  clause({ -x + a > 0, x + b >= 0,  x - c >= 0 }) })
      .expected(exactly(
            clause({ a + b >= 0, a - c >= 0 })
      ))
      .premiseRedundant(true)
    )


TEST_GENERATION(ported_lra_test_basic05_neg,
    Generation::SymmetricTest()
      .inputs ({  clause({ x + a > 0, -x + b >= 0, - x - c >= 0 }) })
      .expected(exactly(
          clause({ (a + b) >= 0, (-b + -c) > 0 }), 
          clause({ (a + -c) >= 0, (b + c) > 0 })
      ))
      .premiseRedundant(true)
    )
  // TODO make optimized version that always selects the "better one" from phi[x] vs phi[-x]
  // ported_lra_test_basic05_neg,
  // ported_lra_test_basic05_pos,


/////////////////////////////////////////////////////////
// Only use unshielded variables
//////////////////////////////////////

TEST_GENERATION(ported_lra_test_shielded01,
    Generation::SymmetricTest()
      .inputs ({  clause({x + a > 0, - x + b > 0, f(x) + c > 0 }) })
      .expected(exactly())
      .premiseRedundant(false)
    )

TEST_GENERATION(ported_lra_test_shielded02,
    Generation::SymmetricTest()
      .inputs ({  clause({ x + a > 0, - x + b > 0, P(x) }) })
      .expected(exactly())
      .premiseRedundant(false)
    )

/////////////////////////////////////////////////////////
// EQ TEST
//////////////////////////////////////

TEST_GENERATION(ported_lra_test_eq01a,
    Generation::SymmetricTest()
      .inputs ({  clause({ x + a >= 0, x - b == 0, P(y) }) })
      .expected(exactly(
            clause({ a + b >= 0, P(y) }),
            clause({ P(y) }) // TODO can we detect redundancies of that kind?
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(ported_lra_test_eq01b,
    Generation::SymmetricTest()
      .inputs ({  clause({ x + a >= 0, - x + b == 0, P(y) }) })
      .expected(exactly(
            clause({ a + b >= 0, P(y) }),
            clause({ P(y) }) // TODO can we detect redundancies of that kind?
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(ported_lra_test_eq02a,
    Generation::SymmetricTest()
      .inputs ({  clause({ x + a > 0, x - b == 0, P(y) }) })
      .expected(exactly(
            clause({ a + b >= 0, P(y) }),
            clause({ P(y) }) // TODO can we detect redundancies of that kind?
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(ported_lra_test_eq02b,
    Generation::SymmetricTest()
      .inputs ({  clause({ x + a > 0, - x + b == 0, P(y) }) })
      .expected(exactly(
            clause({ a + b >= 0, P(y) }),
            clause({ P(y) }) // TODO can we detect redundancies of that kind?
      ))
      .premiseRedundant(true)
    )


TEST_GENERATION(ported_lra_test_eq03a,
    Generation::SymmetricTest()
      .inputs ({  clause({ -x + a > 0, x - b == 0, P(y) }) })
      // elim set: { a, b + ε, -∞ }
      .expected(exactly(
                  //   clause({ -x + a > 0, x - b == 0, P(y) })[x // -∞]
                  // = clause({ true      , false     , P(y) })
                  // ==> redundant
                  //
                  //   clause({ -x + a > 0, x - b == 0, P(y) })[x // a]
                  // = clause({ -a + a > 0, a - b == 0, P(y) })
                  // = clause({             a - b == 0, P(y) })
                  clause({ a - b == 0, P(y) })
                  //
                  //   clause({ -x + a > 0, x - b == 0, P(y) })[x // b + ε]
                  // = clause({ -b - ε + a > 0, b + ε - b == 0, P(y) })
                  // = clause({ -b + a - ε > 0,     ε     == 0, P(y) })
                  // = clause({ -b + a     > 0,                 P(y) })
                , clause({ -b + a > 0, P(y) })
      ))
      .premiseRedundant(true)
    )


TEST_GENERATION(ported_lra_test_eq03a_neg,
    Generation::SymmetricTest()
      .inputs ({  clause({ x + a > 0, -x + b == 0, P(y) }) })
      // elim set: { a, -∞ }
      .expected(exactly(
                  clause({             P(y) })
                , clause({ b + a >= 0, P(y) }) // TODO can we somehow detect redundncies like this?
      ))
      .premiseRedundant(true)
    )

/////////////////////////////////////////////////////////
// NOT EQ TEST
//////////////////////////////////////


TEST_GENERATION(ported_lra_test_neq1a,
    Generation::SymmetricTest()
      .inputs ({  clause({ 0 != x + a , 0 != x + b })})
      .expected(exactly(
             clause({ 0 != a - b })
           , clause({ 0 != a - b }) // TODO optimization
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(ported_lra_test_neq1b,
    Generation::SymmetricTest()
      .inputs ({  clause({ 0 != -x - a , 0 != x + b })})
      .expected(exactly(
            clause({ 0 != a - b })
          , clause({ 0 != a - b }) // TODO optimization
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(ported_lra_test_neq1c,
    Generation::SymmetricTest()
      .inputs ({  clause({ 0 != -x - a , 0 != -x - b })})
      .expected(exactly(
            clause({ 0 != a - b })
          , clause({ 0 != a - b }) // TODO optimization
      ))
      .premiseRedundant(true)
    )


TEST_GENERATION(ported_lra_test_neq1d,
    Generation::SymmetricTest()
      .inputs ({  clause({ 0 != x + a , 0 != -x - b })})
      .expected(exactly(
            clause({ 0 != a - b })
          , clause({ 0 != a - b }) // TODO optimization
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(ported_lra_test_neq2,
    Generation::SymmetricTest()
      .inputs ({  clause({ 0 != 2 * x + a , 0 != -x - b })})
      .expected(exactly(
            clause({ 0 != frac(1,2) * a - b })
          , clause({ 0 != frac(1,2) * a - b }) // TODO optimization
      ))
      .premiseRedundant(true)
    )


TEST_GENERATION(ported_lra_test_misc02,
    Generation::SymmetricTest()
      .inputs ({  clause({ 0 != 30 * x +          f2(y,z) , 0 != 2 * x +       y })})
      .expected(exactly(
                 clause({ 0 != -15 * y +  f2(y,z)  }), // TODO optimization for this case
                 clause({ 0 !=  15 * y + -f2(y,z)  })
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(ported_lra_test_bug02a,
    Generation::SymmetricTest()
      .inputs ({  clause({ 0 == y + -1 , 0 != y + -c })})
      .expected(exactly(
            clause({ -c + 1 == 0             })
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(ported_lra_test_bug03,
    Generation::SymmetricTest()
      .inputs ({  clause({ 0 != -1 + -x + -3 * f(x) + y 
                             , 0 !=  1 +  x +  3 * f(x) - y })})
      .expected(exactly(
            clause({  })
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(ported_lra_test_bug04,
    Generation::SymmetricTest()
      // .inputs ({         clause({ y - x >= 0, x - z >= 0, f(z) - f(y) > 0})})
      .inputs ({         clause({ -x + y >= 0, x + -z >= 0, -f(y) + f(z) > 0 })})
      .expected(exactly( clause({ y             - z >= 0, f(z) - f(y) > 0}) ))
      .premiseRedundant(true)
    )

// TEST_GENERATION(ported_lra_test_bug05,
//     Generation::SymmetricTest()
//     .inputs({clause({
//           -5 * x + e + -4 * f(z) + -7 * b >= 0,
//           -4 * x +  -19 * g(z) + - c * y  + - (d * f(z)) >= 0,
//           15 + 15 * x + 6 * y + -17 * b >= 0,
//         })
//       })
//     // elimSet 
//     //  1/5 * e + -4/5 * f(z) - 7/5 * b + ε
//     //  -19/4 * g(z) - 1/4 * c * y - 1/4 * d * f(z) + ε
//     //  -∞
//       .expected(exactly( 
//           // clause[x//-∞] = true
//           // clause[x//1/5 * e + -4/5 * f(z) - 7/5 * b + ε] 
//           // = -4 * x +  -19 * g(z) + - c * y  + - (d * f(z)) >= 0 \/ 15 + 15 * x + 6 * y + -17 * b >= 0 [x // 1/5 * e + -4/5 * f(z) - 7/5 * b + ε]
//           // = -4 * (1/5 * e + -4/5 * f(z) - 7/5 * b + ε) +  -19 * g(z) + - c * y  + - (d * f(z)) >= 0 \/ 15 + 15 * (1/5 * e + -4/5 * f(z) - 7/5 * b + ε) + 6 * y + -17 * b >= 0
//           // = -4/5 * e + 16/5 * f(z) + 28/5 * b - ε +  -19 * g(z) + - c * y  + - (d * f(z)) >= 0 \/ 15 + 3 * e + -12/5 * f(z) - 21/5 * b + ε + 6 * y + -17 * b >= 0
//           // = -4/5 * e + 16/5 * f(z) + 28/5 * b +  -19 * g(z) + - c * y  + - (d * f(z)) - ε >= 0 \/ 15 + 3 * e + -12/5 * f(z) - 21/5 * b + 6 * y + -17 * b + ε >= 0
//           // = -4/5 * e + 16/5 * f(z) + 28/5 * b +  -19 * g(z) + - c * y  + - (d * f(z))     >  0 \/ 15 + 3 * e + -12/5 * f(z) - 21/5 * b + 6 * y + -17 * b     >= 0
//           clause({ -frac(4,5) * e + frac(16,5) * f(z) + frac(28,5) * b +  -19 * g(z) + - c * y  + - (d * f(z)) > 0,  15 + 3 * e + -frac(12,5) * f(z) - frac(21,5) * b + 6 * y + -17 * b >= 0 })
//           // clause[ x // -19/4 * g(z) - 1/4 * c * y - 1/4 * d * f(z) + ε ] = 
//           // = -5 * x + e + -4 * f(z) + -7 * b >= 0 \/  15 + 15 * x + 6 * y + -17 * b >= 0 [ x // -19/4 * g(z) - 1/4 * c * y - 1/4 * d * f(z) + ε ]
//           // = -5 * (-19/4 * g(z) - 1/4 * c * y - 1/4 * d * f(z) + ε) + e + -4 * f(z) + -7 * b >= 0 \/  15 + 15 * (-19/4 * g(z) - 1/4 * c * y - 1/4 * d * f(z) + ε) + 6 * y + -17 * b >= 0
//           // = 95/4 * g(z) + 5/4 * c * y + 5/4 * d * f(z) - ε + e + -4 * f(z) + -7 * b >= 0 \/  15 + -285/4 * g(z) - 15/4 * c * y - 15/4 * d * f(z) + ε + 6 * y + -17 * b >= 0
//           // = 95/4 * g(z) + 5/4 * c * y + 5/4 * d * f(z) + e + -4 * f(z) + -7 * b - ε >= 0 \/  15 + -285/4 * g(z) - 15/4 * c * y - 15/4 * d * f(z) + 6 * y + -17 * b + ε >= 0
//           // = 95/4 * g(z) + 5/4 * c * y + 5/4 * d * f(z) + e + -4 * f(z) + -7 * b     >  0 \/  15 + -285/4 * g(z) - 15/4 * c * y - 15/4 * d * f(z) + 6 * y + -17 * b     >= 0
//           ,clause({frac(95,4) * g(z) + frac(5,4) * c * y + frac(5,4) * d * f(z) + e + -4 * f(z) + -7 * b     >  0,  15 + -frac(285,4) * g(z) - frac(15,4) * c * y - frac(15,4) * d * f(z) + 6 * y + -17 * b     >= 0})
//           // clause({
//           //  1 + frac(6,15) * y + frac(-17,15) * b + frac(1,5) * e + frac(-4,5) * f(z) + frac(-7,5) * b >= 0,
//           //  1 + frac(6,15) * y + frac(-17,15) * b + frac(-19,4) * g(z) + frac(-1,4) * c * y  + frac(-1,4) * (d * f(z)) >= 0,
//           //     }) 
//           ))
//       .premiseRedundant(true)
//     )



TEST_GENERATION(to_optimize_2,
    Generation::SymmetricTest()
      .inputs ({  clause({ 0 != a - x, 0 != b - x })})
      .expected(exactly(
                   clause({ 0 != b - a  })
                 , clause({ 0 != a - b  }) 
        // TODO optimization for this case to only one of the two results
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(to_optimize_3,
    Generation::SymmetricTest()
      .inputs ({  clause({ 0 != a - x, 0 != b - x, 0 != c - x })})
      .expected(exactly(
                   clause({             0 != b - a, 0 != c - a  })
                 , clause({ 0 != a - b            , 0 != c - b  }) 
                 , clause({ 0 != a - c, 0 != b - c              })
        // TODO optimization for this case to only one of the three results
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(to_optimize_4,
    Generation::SymmetricTest()
      .inputs ({  clause({ 0 != a - x, 0 != b - x, 0 != c - x, 0 != d - x })})
      .expected(exactly(
                   clause({             0 != b - a, 0 != c - a, 0 != d - a  })
                 , clause({ 0 != a - b            , 0 != c - b, 0 != d - b  })
                 , clause({ 0 != a - c, 0 != b - c            , 0 != d - c  })
                 , clause({ 0 != a - d, 0 != b - d, 0 != c - d              })
        // TODO optimization for this case to only one of the four results
      ))
      .premiseRedundant(true)
    )


  // TODO test -x + bla == 0 vs -x + -bla == 0



#define NOT_APPLICABLE_TEST(i, lit)                                                       \
  TEST_GENERATION(not_applicable_ ## i,                                                   \
      Generation::SymmetricTest()                                                         \
        .inputs ({         clause({ x > 0, lit })})                                       \
        .expected(exactly())                                                              \
        .premiseRedundant(false)                                                          \
      )                                                                                   \

NOT_APPLICABLE_TEST(1, P(x))
NOT_APPLICABLE_TEST(2, f(x) + a > 0)
NOT_APPLICABLE_TEST(4, (x * y) > 0)
NOT_APPLICABLE_TEST(5, (x * x) > 0)
NOT_APPLICABLE_TEST(6, isInt(x))

TEST_GENERATION(lira_01,
    Generation::SymmetricTest()
      // .inputs ({         clause({ y - x >= 0, x - z >= 0, f(z) - f(y) > 0})})
      .inputs ({         clause({ floor(a) + frac(1,3) - x > 0, x  -  floor(a) - frac(2,3) > 0 , b - ceil(x) + x > 0 })})
      .expected(exactly( clause({ b > frac(2,3) }) ))
      .premiseRedundant(true)
    )


TEST_GENERATION(lia_01_1,
    Generation::SymmetricTest()
      .inputs ({         clause({ 3 * floor(x) - 1 == 0 })})
      .expected(withoutDuplicates(exactly( clause({ }) )))
      .premiseRedundant(true)
    )

TEST_GENERATION(lia_01_2,
    Generation::SymmetricTest()
      .inputs ({         clause({ 3 * floor(x) - 1 != 0 })})
      .expected(withoutDuplicates(exactly()))
      .premiseRedundant(true)
    )

TEST_GENERATION(lia_02,
    Generation::SymmetricTest()
      .inputs ({         clause({ 3 * floor(x) - 1 != 0, x - floor(a) > 0, floor(b) - x > 0 })})
      // elimSet: 1, 1 + ε, 4/3, 1/3
      //          -∞
      //          floor(b)
      .expected(withoutDuplicates(exactly( 
             // clause({ 3 * floor(x) - 1 != 0, x - floor(a) > 0, floor(b) - x > 0 })[-inf]
             // => redundant
             // clause({ 3 * floor(x) - 1 != 0, x - floor(a) > 0, floor(b) - x > 0 })[floor(b)]
                clause({ 3 * floor(b) - 1 != 0, floor(b) - floor(a) > 0                  })
             // clause({ 3 * floor(x) - 1 != 0, x - floor(a) > 0, floor(b) - x > 0 })[1]
             //          ^^^^^^^^^^^^^^^^^^^^^----> redundant
             // clause({ 3 * floor(x) - 1 != 0, x - floor(a) > 0, floor(b) - x > 0 })[1 + epsilon]
             //          ^^^^^^^^^^^^^^^^^^^^^----> redundant
             // clause({ 3 * floor(x) - 1 != 0, x - floor(a) > 0, floor(b) - x > 0 })[4/3]
             //          ^^^^^^^^^^^^^^^^^^^^^----> redundant
             // clause({ 3 * floor(x) - 1 != 0, x - floor(a) > 0, floor(b) - x > 0 })[1/3]
             //          ^^^^^^^^^^^^^^^^^^^^^----> redundant
            )))
      .premiseRedundant(true)
    )

#define liraQuot(l,r) floor((l) / (r))
#define liraRem(l,r) (l) - ((r) * liraQuot(l, r))

TEST_GENERATION(lia_03,
    Generation::SymmetricTest()
      .inputs ({         clause({ liraRem(x, 3)  - 1 != 0, x - 3 * floor(a) > 0, 3 * floor(b) - x > 0 })})
      // elimSet = { 3 Z + 0, 3 Z + 1, 3 * floor(b), -infty }
      .expected(withoutDuplicates(exactly( 
          // clause({ liraRem(x, 3)  - 1 != 0, x - 3 * floor(a) > 0, 3 * floor(b) - x > 0 })[x // 3 Z]
          //          ^^^^^^^^^^^^^^^^^^--> redundant 
          //
          // clause({ liraRem(x, 3)  - 1 != 0, x - 3 * floor(a) > 0, 3 * floor(b) - x > 0 })[x // 3 Z + 1]
          // clause({                          x - 3 * floor(a) > 0, 3 * floor(b) - x > 0 })[x // 3 * floor(b) + 1]
          // clause({           3 * floor(b) + 1 - 3 * floor(a) > 0                       })
             clause({           3 * floor(b) + 1 - 3 * floor(a) > 0                       })
          // clause({                          x - 3 * floor(a) > 0, 3 * floor(b) - x > 0 })[x // 3 * floor(b) + 4]
          ,  clause({           3 * floor(b) + 4 - 3 * floor(a) > 0                       })  // TODO do we really need this one as well or can we optimize it away?

          // clause({ liraRem(x, 3)  - 1 != 0, x - 3 * floor(a) > 0, 3 * floor(b) - x > 0 })[x // 3 * floor(b)]
          //          ^^^^^^^^^^^^^^^^^^^^^^^--> redundant
          //
          // clause({ liraRem(x, 3)  - 1 != 0, x - 3 * floor(a) > 0, 3 * floor(b) - x > 0 })[x // -infty]
          // redundant <---------------------------------------------^^^^^^^^^^^^^^^^^^^^
           )))
      .premiseRedundant(true)
    )

TEST_GENERATION(test_misc_01,
    Generation::SymmetricTest()
      .inputs ({         clause({ x + f(a) > 0 })})
      .expected(withoutDuplicates(exactly( 
             clause({  })
           )))
      .premiseRedundant(true)
    )

TEST_GENERATION(test_misc_02,
    Generation::SymmetricTest()
      .inputs ({         clause({ x + f(x) > 0 })})
      .expected(withoutDuplicates(exactly( )))
      .premiseRedundant(false)
    )

#define TEST_INTERNAL(Num)                                                                \
  TEST_FUN(viras_internal_ ## Num) {                                                      \
    auto conf = VampireVirasConfig<Num ## Traits>();                                      \
    auto viras = viras::viras_test(conf);                                                 \
    auto success = viras.auto_test();                                                     \
    ASS(success)                                                                          \
  }                                                                                       \

TEST_INTERNAL(Real)
TEST_INTERNAL(Rat)

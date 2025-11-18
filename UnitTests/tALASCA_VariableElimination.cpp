/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Test/SyntaxSugar.hpp"
#include "Inferences/ALASCA/VariableElimination.hpp"

#include "Test/SyntaxSugar.hpp"
#include "Test/AlascaTestUtils.hpp"
#include "Test/GenerationTester.hpp"

using namespace std;
using namespace Kernel;
using namespace Inferences;
using namespace Test;
using namespace Indexing;
using namespace Inferences::ALASCA;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// TEST CASES 
/////////////////////////////////////

#define SUGAR(Num)                                                                                            \
  NUMBER_SUGAR(Num)                                                                                           \
  DECL_DEFAULT_VARS                                                                                           \
  DECL_FUNC(f, {Num}, Num)                                                                                    \
  DECL_FUNC(g, {Num}, Num)                                                                                    \
  DECL_FUNC(f2, {Num, Num}, Num)                                                                               \
  DECL_CONST(a, Num)                                                                                          \
  DECL_CONST(b, Num)                                                                                          \
  DECL_CONST(c, Num)                                                                                          \
  DECL_CONST(d, Num)                                                                                          \
  DECL_CONST(e, Num)                                                                                          \
  DECL_PRED(R, {Num,Num})                                                                                     \
  DECL_PRED(P, {Num})                                                                                         \

#define MY_SYNTAX_SUGAR SUGAR(Rat)

REGISTER_GEN_TESTER(AlascaGenerationTester<VariableElimination>())

/////////////////////////////////////////////////////////
// Basic tests
//////////////////////////////////////

TEST_GENERATION(basic01,
    Generation::SymmetricTest()
      .inputs ({  clause({x + a > 0, x + b > 0 }) })
      .expected(exactly(
            clause({})
      ))
      .premiseRedundant(true)
    )
TEST_GENERATION(basic02,
    Generation::SymmetricTest()
      .inputs ({  clause({x + a > 0, - x + b > 0 }) })
      .expected(exactly(
            clause({ a + b > 0 })
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(basic03,
    Generation::SymmetricTest()
      .inputs ({  clause({x + a > 0, - x + b > 0, f(y) + c > 0 }) })
      .expected(exactly(
        clause({a + b > 0, f(y) + c > 0 }) 
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(basic04,
    Generation::SymmetricTest()
      .inputs ({  clause({ x + a > 0, -x + b >= 0, x + c >= 0 }) })
      .expected(exactly(
            clause({ a + b >= 0, b + c >= 0 })
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(basic05,
    Generation::SymmetricTest()
      .inputs ({  clause({ x + a > 0, -x + b >= 0, - x - c >= 0 }) })
      .expected(exactly(
            clause({ a + b >= 0, a - c >= 0 })
      ))
      .premiseRedundant(true)
    )


/////////////////////////////////////////////////////////
// Only use unshielded variables
//////////////////////////////////////

TEST_GENERATION(shielded01,
    Generation::SymmetricTest()
      .inputs ({  clause({x + a > 0, - x + b > 0, f(x) + c > 0 }) })
      .expected(exactly())
      .premiseRedundant(false)
    )

TEST_GENERATION(shielded02,
    Generation::SymmetricTest()
      .inputs ({  clause({ x + a > 0, - x + b > 0, P(x) }) })
      .expected(exactly())
      .premiseRedundant(false)
    )

/////////////////////////////////////////////////////////
// EQ TEST
//////////////////////////////////////

TEST_GENERATION(eq01a,
    Generation::SymmetricTest()
      .inputs ({  clause({ x + a >= 0, x - b == 0, P(y) }) })
      .expected(exactly(
            clause({ a + b >= 0, P(y) }),
            clause({ P(y) }) // TODO can we detect redundancies of that kind?
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(eq01b,
    Generation::SymmetricTest()
      .inputs ({  clause({ x + a >= 0, - x + b == 0, P(y) }) })
      .expected(exactly(
            clause({ a + b >= 0, P(y) }),
            clause({ P(y) }) // TODO can we detect redundancies of that kind?
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(eq02a,
    Generation::SymmetricTest()
      .inputs ({  clause({ x + a > 0, x - b == 0, P(y) }) })
      .expected(exactly(
            clause({ a + b >= 0, P(y) }),
            clause({ P(y) }) // TODO can we detect redundancies of that kind?
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(eq02b,
    Generation::SymmetricTest()
      .inputs ({  clause({ x + a > 0, - x + b == 0, P(y) }) })
      .expected(exactly(
            clause({ a + b >= 0, P(y) }),
            clause({ P(y) }) // TODO can we detect redundancies of that kind?
      ))
      .premiseRedundant(true)
    )


TEST_GENERATION(eq03a,
    Generation::SymmetricTest()
      .inputs ({  clause({ -x + a > 0, x - b == 0, P(y) }) })
      .expected(exactly(
            clause({ P(y) }), // TODO can we detect redundancies of that kind?
            clause({ a - b >= 0, P(y) })
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(eq03b,
    Generation::SymmetricTest()
      .inputs ({  clause({ -x + a > 0, - x + b == 0, P(y) }) })
      .expected(exactly(
            clause({ P(y) }), // TODO can we detect redundancies of that kind?
            clause({ a - b >= 0, P(y) })
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(eq04a,
    Generation::SymmetricTest()
      .inputs ({  clause({ x + a > 0, -x + b >= 0, - x - c == 0 }) })
      .expected(exactly(
            clause({ a + b >= 0, a - c >= 0 }),
            clause({ a + b >= 0, b + c >= 0 })
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(eq04b,
    Generation::SymmetricTest()
      .inputs ({  clause({ x + a > 0, -x + b >= 0, x + c == 0 }) })
      .expected(exactly(
            clause({ a + b >= 0, a - c >= 0 }),
            clause({ a + b >= 0, b + c >= 0 })
      ))
      .premiseRedundant(true)
    )

/////////////////////////////////////////////////////////
// NOT EQ TEST
//////////////////////////////////////


TEST_GENERATION(neq1a,
    Generation::SymmetricTest()
      .inputs ({  clause({ 0 != x + a , 0 != x + b })})
      .expected(exactly(
            clause({ 0 != a - b })
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(neq1b,
    Generation::SymmetricTest()
      .inputs ({  clause({ 0 != -x - a , 0 != x + b })})
      .expected(exactly(
            clause({ 0 != a - b })
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(neq1c,
    Generation::SymmetricTest()
      .inputs ({  clause({ 0 != -x - a , 0 != -x - b })})
      .expected(exactly(
            clause({ 0 != a - b })
      ))
      .premiseRedundant(true)
    )


TEST_GENERATION(neq1d,
    Generation::SymmetricTest()
      .inputs ({  clause({ 0 != x + a , 0 != -x - b })})
      .expected(exactly(
            clause({ 0 != a - b })
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(neq2,
    Generation::SymmetricTest()
      .inputs ({  clause({ 0 != 2 * x + a , 0 != -x - b })})
      .expected(exactly(
            clause({ 0 != frac(1,2) * a - b })
      ))
      .premiseRedundant(true)
    )

  // TODO


/////////////////////////////////////////////////////////
// MISC
//////////////////////////////////////

TEST_GENERATION(misc01,
    Generation::SymmetricTest()
      .inputs ({  clause({ 0 != -3 * x +               f2(y,z) , 0 != x + -10 * z })})
                       // 0 !=      x +        -(1/3) f2(y,z) , 0 != x + -10 * z
      .expected(exactly(anyOf(
            clause({ 0 !=  10 * z + frac(-1, 3) * f2(y,z) }), 
            clause({ 0 != -10 * z + frac( 1, 3) * f2(y,z) })
      )))
      .premiseRedundant(true)
    )

// 81627. 0.0 != ((30.0 * X0) + lG159(X1,X2)) | 0.0 != ((2.0 * X0) + X1) <- (49) [inequality normalization 81626]
// 81656. 0.0 != ((-0.5 * X1) + (0.0333333 * lG159(X1,X2))) <- (49) [inequality variable elimination 81627]

TEST_GENERATION(misc02,
    Generation::SymmetricTest()
      .inputs ({  clause({ 0 != 30 * x +          f2(y,z) , 0 != 2 * x +       y })})
                     // { 0 !=      x + (1/30) * f2(y,z) , 0 !=     x + (1/2) y }
      .expected(exactly(anyOf(
                 clause({ 0 != frac(-1,2) * y + frac(1,30) * f2(y,z) })
      )))
      .premiseRedundant(true)
    )

/////////////////////////////////////////////////////////
// Bugs
//////////////////////////////////////



// TEST_GENERATION(bug01a,
//     Generation::SymmetricTest()
//       .inputs ({  clause({ x + a > 0, -x + b >= 0, x + c == 0 }) })
//       .expected(exactly(
//                 // 0 = $sum($uminus(X2),$sum(X3,-1)) | 0 != $sum(X3,$uminus(len(cons(X0,X1)))) | 0 != $sum(X2,$uminus(len(X1)))
//                 // 0 = -X2 + X3 + -1 | 0 != X3 + -len(cons(X0,X1)) | 0 != X2 + -len(X1)
//                 // { 0 == -x + y + -1 , 0 != y + -c , 0 != x + -b }
//                 // { 0 == -x + y + -1 , 0 != y + -c , 0 != x + -b }
//             clause({ 0 == -x + y + -1 , 0 != y + -c , 0 != x + -b }),
//             // clause({ a + b >= 0, b + c >= 0 })
//       ))
//       .premiseRedundant(true)
//     )
//
// TEST_GENERATION(bug01b,
//     Generation::SymmetricTest()
//       .inputs ({  clause({ x + a > 0, -x + b >= 0, x + c == 0 }) })
//       .expected(exactly(
//                 // { 0 == -x + y + -1 , 0 != y + -c , 0 != x + -b }
//                 // { 0 == -x + y + -1 , y + -c > 0 , -y +  c > 0, x + -b > 0, -x + b > 0 }
//             clause({ 0 == -x + y + -1 , 0 != y + -c , 0 != x + -b }),
//          // clause({ a + b >= 0, b + c >= 0 })
//       ))
//       .premiseRedundant(true)
//     )
//
// TEST_GENERATION(bug01c,
//     Generation::SymmetricTest()
//       .inputs ({  clause({ x + a > 0, -x + b >= 0, x + c == 0 }) })
//       .expected(exactly(
//                     // { 0 == -x + y + -1 , 0 != y + -c , 0 != x + -b }
//                     // { -x + y + -1 >= 0 , y + -c > 0 , -y +  c > 0, x + -b > 0, -x + b > 0 }
//             clause({ -x + y + -1 >= 0 , y + -c > 0 , -y +  c > 0, x + -b > 0, -x + b > 0 })
//             // clause({ a + b >= 0, b + c >= 0 })
//       ))
//       .premiseRedundant(true)
//     )
//
// TEST_GENERATION(bug01d,
//     Generation::SymmetricTest()
//       .inputs ({  clause({ x + a > 0, -x + b >= 0, x + c == 0 }) })
//       .expected(exactly(
//                 // { 0 == -x + y + -1 , 0 != y + -c , 0 != x + -b }
//                 // { x + -y + 1 >= 0 , y + -c > 0 , -y +  c > 0, x + -b > 0, -x + b > 0 }
//             clause({ x + -y + 1 >= 0 , y + -c > 0 , -y +  c > 0, x + -b > 0, -x + b > 0 })
//             // clause({ a + b >= 0, b + c >= 0 })
//       ))
//       .premiseRedundant(true)
//     )


TEST_GENERATION(bug02a,
    Generation::SymmetricTest()
      .inputs ({  clause({ 0 == y + -1 , 0 != y + -c })})
            //     { 0 == y + -1 , y + -c > 0 , -y + c > 0 }
            //     { y + -1 >= 0, y + -c > 0 , -y + c > 0 } /\ { -y + 1 >= 0, y + -c > 0 , -y + c > 0 }
            //     { c + -1 >= 0, c + -c > 0 }              /\ { -y + -c >= 0, c + -c > 0             }
            //     { c + -1 >= 0             }              /\ {  1 + -c >= 0                         }
      .expected(exactly(
            clause({ c + -1 >= 0             }), // TODO potential optimization for this
            clause({ 1 + -c >= 0             })
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(bug03,
    Generation::SymmetricTest()
      .inputs ({  clause({ 0 != -1 + -x + -3 * f(x) + y , 0 != 1 + x + 3 * f(x) - y })})
      .expected(exactly(
            clause({ 0 != 1 + 3 * f(x) + x + -1 - x + -3 * f(x) })
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(bug04,
    Generation::SymmetricTest()
      // .inputs ({         clause({ y - x >= 0, x - z >= 0, f(z) - f(y) > 0})})
      .inputs ({         clause({ -x + y >= 0, x + -z >= 0, -f(y) + f(z) > 0 })})
      .expected(exactly( clause({ y             - z >= 0, f(z) - f(y) > 0}) ))
      .premiseRedundant(true)
    )

TEST_GENERATION(bug05,
    Generation::SymmetricTest()
//     (assert (forall ((x4 Real)(y Real)(z Real)(x2 Real)(x Real))(or false
//   (>= (+ (* (/ 11 1) y) (+ a (* (/ 14 1) z))) (/ 0 1))
//   (>= (+ (* (-(/ 5 1)) x) (+ e (+ (* (-(/ 4 1)) f(z)) (* (-(/ 7 1)) b)))) (/ 0 1))
//   (>= (+ (* (-(/ 4 1)) x) (+ (* (-(/ 19 1)) g(z)) (+ (- (* c y)) (- (* d f(z)))))) (/ 0 1))
//   (>= (+ (/ 15 1) (+ (* (/ 15 1) x) (+ (* (/ 6 1) y) (* (-(/ 17 1)) b)))) (/ 0 1))
//   )))
    .inputs({clause({
          // 11 * y + a + 14 *  z >= 0
          -5 * x + e + -4 * f(z) + -7 * b >= 0,
          -4 * x +  -19 * g(z) + - c * y  + - (d * f(z)) >= 0,
          15 + 15 * x + 6 * y + -17 * b >= 0,
        })
      })
//
//
// ;- rule: alasca variable elimination
//
// ;- unit id: 3469
// (assert (not (forall ((x4 Real)(y Real)(z Real)(x2 Real))(or false
//   -- (>= (+ (* (/ 11 1) y) (+ a (* (/ 14 1) z))) (/ 0 1))
//   (>= (+ (* (-(/ 7 5)) b) (+ (* (-(/ 4 5)) f(z)) (+ (* (/ 1 5) e) (+ (* (-(/ 17 15)) b) (+ (* (/ 2 5) y) (/ 1 1)))))) (/ 0 1))
//   (>= (+ (* (-(/ 1 4)) (* d f(z))) (+ (* (-(/ 1 4)) (* c y)) (+ (* (-(/ 19 4)) g(z)) (+ (* (-(/ 17 15)) b) (+ (* (/ 2 5) y) (/ 1 1)))))) (/ 0 1))
//   ))))
// (check-sat)
      // .inputs ({         clause({ y - x >= 0, x - z >= 0, f(z) - f(y) > 0})})
      .expected(exactly( clause({
          // -x + 1/5 * e + -4/5 * f(z) + -7/5 * b >= 0
          // -x +  -19/4 * g(z) + - 1/4 * c * y  + -1/4 * (d * f(z)) >= 0
          //  x + 1 + 6/15 * y + -17/15 * b >= 0
           /////////
           1 + frac(6,15) * y + frac(-17,15) * b + frac(1,5) * e + frac(-4,5) * f(z) + frac(-7,5) * b >= 0,
           1 + frac(6,15) * y + frac(-17,15) * b + frac(-19,4) * g(z) + frac(-1,4) * c * y  + frac(-1,4) * (d * f(z)) >= 0,
              }) ))
      .premiseRedundant(true)
    )




  // TODO test -x + bla == 0 vs -x + -bla == 0

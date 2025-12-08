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
#include "Inferences/ALASCA/Superposition.hpp"
#include "Lib/STL.hpp"

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
  DECL_DEFAULT_VARS                                                                       \
  DECL_VAR(x0, 0)                                                                         \
  DECL_VAR(x1, 1)                                                                         \
  DECL_VAR(x2, 2)                                                                         \
  DECL_VAR(x3, 3)                                                                         \
  DECL_VAR(x4, 4)                                                                         \
  DECL_VAR(x5, 5)                                                                         \
  DECL_VAR(x6, 5)                                                                         \
  DECL_VAR(x7, 5)                                                                         \
  DECL_VAR(x8, 5)                                                                         \
  DECL_VAR(x9, 5)                                                                         \
  DECL_VAR(x10, 5)                                                                        \
  DECL_VAR(x11, 5)                                                                        \
  DECL_VAR(x12, 5)                                                                        \
  DECL_VAR(x13, 5)                                                                        \
  DECL_FUNC(f, {Num}, Num)                                                                \
  DECL_FUNC(g, {Num}, Num)                                                                \
  DECL_FUNC(f2, {Num, Num}, Num)                                                          \
  DECL_FUNC(g2, {Num, Num}, Num)                                                          \
  DECL_FUNC(f4, {Num, Num, Num, Num}, Num)                                                \
  DECL_FUNC(g4, {Num, Num, Num, Num}, Num)                                                \
  DECL_CONST(a, Num)                                                                      \
  DECL_CONST(b, Num)                                                                      \
  DECL_CONST(c, Num)                                                                      \
  DECL_CONST(c0, Num)                                                                     \
  DECL_CONST(c1, Num)                                                                     \
  DECL_CONST(c2, Num)                                                                     \
  DECL_CONST(c3, Num)                                                                     \
  DECL_CONST(c4, Num)                                                                     \
  DECL_CONST(c5, Num)                                                                     \
  DECL_CONST(c6, Num)                                                                     \
  DECL_CONST(c7, Num)                                                                     \
  DECL_CONST(c8, Num)                                                                     \
  DECL_CONST(c9, Num)                                                                     \
  DECL_CONST(c10, Num)                                                                    \
  DECL_CONST(c11, Num)                                                                    \
  DECL_CONST(c12, Num)                                                                    \
  DECL_CONST(c13, Num)                                                                    \
  DECL_CONST(c14, Num)                                                                    \
  DECL_PRED(p, {Num})                                                                     \
  DECL_PRED(r, {Num,Num})                                                                 \
                                                                                          \
  DECL_SORT(alpha)                                                                        \
  DECL_FUNC(fa, {Num}, alpha)                                                             \
  DECL_PRED(pa, {alpha})                                                                  \
  DECL_FUNC(ga, {Num, Num}, alpha)                                                        \
  DECL_CONST(aa, alpha)                                                                   \
  DECL_CONST(ba, alpha)                                                                   \
  DECL_FUNC(fn, {alpha}, Num)                                                             \

#define MY_SYNTAX_SUGAR SUGAR(Rat)

#define UWA_MODE Options::UnificationWithAbstraction::ALASCA_MAIN

Generation::TestIndices alascaSuperpositionIndices()
{ return {
    [](const SaturationAlgorithm&){ return new AlascaIndex<Superposition::Lhs>();},
    [](const SaturationAlgorithm&){ return new AlascaIndex<Superposition::Rhs>();},
  }; }

auto testSuperposition(Options::UnificationWithAbstraction uwa, bool simultaneous = false)
{ 
  auto s = testAlascaState(uwa);
  auto n = ALASCA::Normalization(s);
  return alascaSimplRule(s,Superposition(s, simultaneous), n);
}



REGISTER_GEN_TESTER(AlascaGenerationTester<Superposition>(testSuperposition(UWA_MODE, /* simultaneous superpos */ false)))

/////////////////////////////////////////////////////////
// Basic tests
//////////////////////////////////////

TEST_GENERATION(basic01,
    Generation::SymmetricTest()
      .indices(alascaSuperpositionIndices())
      .inputs  ({ clause({ selected( 3 * f(x) - 4 - a == 0 )  }) 
                , clause({ selected(     3 * f(x) >  0 )  }) })
      .expected(exactly(
            clause({ 4 + a > 0  })
      ))
    )

TEST_GENERATION(basic02,
    Generation::SymmetricTest()
      .indices(alascaSuperpositionIndices())
      .inputs  ({ clause({ selected( 3 * f(x) - 4 * a == 0 )  })
                , clause({ selected(     f(x) + b >  0 )  }) })
      .expected(exactly(
            clause({ frac(4, 3) * a + b > 0  })
      ))
    )

TEST_GENERATION(basic03,
    Generation::SymmetricTest()
      .indices(alascaSuperpositionIndices())
      .inputs  ({ clause({selected( f(a) + a + 3 == 0 ) })
                , clause({selected( f(x) > 0 ) }) })
      .expected(exactly(
            clause({ - a + -3 > 0  })
      ))
    )

TEST_GENERATION(basic04,
    Generation::SymmetricTest()
      .indices(alascaSuperpositionIndices())
      .inputs  ({ clause({ selected( f(a) + a + 3 == 0 ) })
                , clause({  f(x) > 0, selected(f(g(x)) > 0) }) })
      .expected(exactly(
      ))
    )

TEST_GENERATION(basic05,
    Generation::SymmetricTest()
      .indices(alascaSuperpositionIndices())
      .inputs  ({ clause({selected( f(a) + a + 3 == 0 ) })
                , clause({selected( p(f(x)) ) }) })
      .expected(exactly(
            clause({ p(- a + -3)  })
      ))
    )

TEST_GENERATION(basic06,
    Generation::SymmetricTest()
      .indices(alascaSuperpositionIndices())
      .inputs  ({ clause({selected( f(a) + a + 3 == 0 ) })
                , clause({selected( g(f(x)) != 0 ) }) })
      .expected(exactly(
            clause({ g(-a + -3) != 0 })
      ))
    )

TEST_GENERATION(basic07,
    Generation::SymmetricTest()
      .indices(alascaSuperpositionIndices())
      .inputs  ({ clause({selected( f(a) + a + 3 == 0 ) })
                , clause({selected( g(3 * f(x)) != 0 ) }) })
      .expected(exactly(
            clause({ g(3 * (-a + -3)) != 0 })
      ))
    )

// • s2σ ⊴ t ∈ active(L[s2]σ)
TEST_GENERATION(basic10,
    Generation::SymmetricTest()
      .indices(alascaSuperpositionIndices())
      .inputs  ({ clause({selected( g2(x, y) + g2(y, y) > 0 ) })
                , clause({selected( g2(a, f(a)) - a == 0 ) }) })
      .expected(exactly(
            // clause({ g(3 * (-a + -3)) != 0 })
          /* nothing */
      ))
    )

TEST_GENERATION(uwa1,
    Generation::SymmetricTest()
      .indices(alascaSuperpositionIndices())
      .inputs  ({ clause({ selected( f(a + b) == 0 )  })
                , clause({ selected(   a - b  == 0 )  }) })
      .expected(exactly(
            clause({ f(a + a) == 0  })
      ))
    )

TEST_GENERATION(self_applications_run_only_once,
    Generation::SymmetricTest()
      .indices(alascaSuperpositionIndices())
      .selfApplications(true)
      .inputs  ({ clause({ selected( f(x) + f(y) == 0 )  }) })
      .expected(exactly(
       
                  clause({ - f(x2) + f(x1) == 0    }) 

                , clause({ -f(x2) + f(x1) == 0 })

                , clause({ -f(x2) + f(x0) == 0 })

                , clause({ -f(x2) + f(x0) == 0 })
      ))
    )


// TODO requires non-linear reasoning
// TEST_GENERATION(misc01,
//     Generation::SymmetricTest()
//       .indices(alascaSuperpositionIndices())
//       .inputs  ({         clause({ selected(0 == -17 + a) })
//                 ,         clause({ selected(-19 + -f(x) + a * y  >= 0) }) })
//       .expected(exactly(  clause({          -19 + -f(y) + 17 * x >= 0  }) ))
//     )

TEST_GENERATION(ordering1_ok_1_simult,
    Generation::SymmetricTest()
      .indices(alascaSuperpositionIndices())
      .rule(move_to_heap(testSuperposition(UWA_MODE, /*simultaneous=*/ true)))
      .inputs  ({         clause({ selected( g2(a,a) == 0 ) })
                ,         clause({ selected( f(g2(x,y)) != 0 ), selected( f(g2(y,x)) != 0 ) }) }) 
      .expected(exactly(  clause({ f(0) != 0, f(0) != 0 }) 
                       ,  clause({ f(0) != 0, f(0) != 0 }) ))
    )

// •    L[s2]σ  ∈ Lit+ and L[s2]σ /⪯ C2σ
//   or L[s2]σ /∈ Lit+ and L[s2]σ /≺ C2σ
TEST_GENERATION(ordering1_ok_1,
    Generation::SymmetricTest()
      .indices(alascaSuperpositionIndices())
      .inputs  ({         clause({ selected( g2(a,a) == 0 ) })
                ,         clause({ selected( f(g2(x,y)) != 0 ), selected( f(g2(y,x)) != 0 ) }) }) 
      .expected(exactly(  clause({ f(0) != 0, f(g2(a,a)) != 0 }) 
                       ,  clause({ f(0) != 0, f(g2(a,a)) != 0 }) ))
    )

TEST_GENERATION(ordering1_ok_2,
    Generation::SymmetricTest()
      .indices(alascaSuperpositionIndices())
      .inputs  ({         clause({ selected( g2(a,a) == 0 ) })
                ,         clause({ selected( -f(g2(x,y)) > 0 ), selected( -f(g2(y,x)) > 0 ) }) }) 
      .expected(exactly(  clause({ -f(0) > 0, -f(g2(a,a)) > 0 }) 
                       ,  clause({ -f(0) > 0, -f(g2(a,a)) > 0 }) ))
    )
TEST_GENERATION(ordering1_fail_1,
    Generation::SymmetricTest()
      .indices(alascaSuperpositionIndices())
      .inputs  ({         clause({ selected( g2(a,a) == 0 ) })
                ,         clause({ selected( f(g2(x,y)) > 0 ), selected( f(g2(y,x)) > 0 ) }) }) 
      .expected(exactly(  /* */ ))
    )
// TEST_GENERATION(ordering1_fail_2,
//     Generation::SymmetricTest()
//       .indices(alascaSuperpositionIndices())
//       .inputs  ({         clause({ g2(a,a) == 0 })
//                 ,         clause({ -f(g2(x,y)) > 0, -f(g2(y,x)) > 0 }) }) 
//       .expected(exactly(  /* nothing */          ))
//     )

// • (±k. s1 + t1 ≈ 0)σ is strictly maximal in Hyp1σ
TEST_GENERATION(ordering2_ok,
    Generation::SymmetricTest()
      .indices(alascaSuperpositionIndices())
      .inputs  ({         clause({ selected( g2(x,y) == 0 ), selected( g2(z,z) == 0 ) })
                ,         clause({ selected( f(g2(a,a)) > 0 ) }) }) 
      .expected(exactly(  clause({ f(0) > 0, g2(x,x) == 0 }) 
                       ,  clause({ f(0) > 0, g2(x,y) == 0 }) ))
    )
TEST_GENERATION(ordering2_fail,
    Generation::SymmetricTest()
      .indices(alascaSuperpositionIndices())
      .inputs  ({         clause({ g2(x,y) == 0, g2(y,x) == 0 })
                ,         clause({ f(g2(a,a)) > 0 }) }) 
      .expected(exactly(  /* nothing */  ))
    )


// •        s1  σ is strictly maximal in terms(s1 + t1)σ
TEST_GENERATION(ordering3_ok,
    Generation::SymmetricTest()
      .indices(alascaSuperpositionIndices())
      .selfApplications(false)
      .inputs  ({         clause({ selected( g2(x,y) + 2 * g2(z,z) == 0 ) })
                ,         clause({ selected( f(g2(a,a)) > 0                   ) }) }) 
      .expected(exactly(  clause({ f(       -2  * g2(z,z)) > 0 }) 
                       ,  clause({ f(frac(-1,2) * g2(x,y)) > 0 }) 
                       ))
    )
TEST_GENERATION(ordering3_fail,
    Generation::SymmetricTest()
      .indices(alascaSuperpositionIndices())
      .selfApplications(false)
      .inputs  ({         clause({  g2(x,y) + g2(y,x) + g2(y,x) == 0 })
                ,         clause({ f(g2(a,a)) > 0 }) }) 
      .expected(exactly(  /* nothing */  ))
    )


TEST_GENERATION(uninterpreted_pred_1,
    Generation::SymmetricTest()
      .indices(alascaSuperpositionIndices())
      .inputs  ({        clause({ selected(   f(x) - 1 == 0 )  })
                ,        clause({ selected( p(f(x)) )          }) })
      .expected(exactly( clause({           p(1)               })
      ))
    )

TEST_GENERATION(uninterpreted_pred_2,
    Generation::SymmetricTest()
      .indices(alascaSuperpositionIndices())
      .inputs  ({        clause({ selected(   f(x) - 1 == 0 )      })
                ,        clause({ selected( p(f(a)) ), f(f(b)) > 0 }) })
      .expected(exactly( clause({           p(1)     , f(f(b)) > 0 }) ))
    )

TEST_GENERATION(uninterpreted_pred_3, // TODO couldn't we replace all occurrences of f(x) instead of the maximal one
    Generation::SymmetricTest()
      .indices(alascaSuperpositionIndices())
      .inputs  ({        clause({ selected(   f(x) - 1 == 0 )      })
                ,        clause({ selected( p(f(x)) ), f(f(x)) > 0 }) })
      .expected(exactly( clause({           p(1)     , f(f(x)) > 0 }) ))
    )

TEST_GENERATION(uninterpreted_sort_1,
    Generation::SymmetricTest()
      .indices(alascaSuperpositionIndices())
      .inputs  ({        clause({ selected( f(x) - 1 == 0  ) })
                ,        clause({ selected( fa(f(x)) == aa ) }) })
      .expected(exactly( clause({           fa(  1 ) == aa   }) ))
    )

TEST_GENERATION(uninterpreted_sort_2,
    Generation::SymmetricTest()
      .selfApplications(false)
      .indices(alascaSuperpositionIndices())
      .inputs  ({        clause({ selected( f(x) - 1 == 0  ) })
                ,        clause({ selected( fa(3 *   f(x)) == aa ) }) })
      .expected(exactly( clause({           fa(3 * num(1)) == aa   }) ))
    )

// 0.0 = $sum(X2,$uminus($quotient($product(X1,X2),X1))) | 0.0 = X1 [theory normalization 6]
// 0.0 = $sum($product(X0,X2),$sum($product(X0,X1),$uminus($product(X0,$sum(X1,X2))))) [theory normalization 3]



TEST_GENERATION(bug01a,
    Generation::SymmetricTest()
      .indices(alascaSuperpositionIndices())
      .selfApplications(false)
      .inputs  ({        clause({ selected(  z + -g2(f2(y, z), y) > 0 ), 0 == y  })
                          // (1) {y -> x, z -> y + z}
                          // ==> { (y + z) + -g2(f2(x, (y + z)), x) > 0 , 0 == x }
                          // (2) {y -> x, z -> z}
                          // ==> { z + -g2(f2(x, z), x) > 0 , 0 == x }
                          // (3) {y -> x, z -> y}
                          // ==> { y + -g2(f2(x, y), x) > 0, 0 == x  }

                ,        clause({ selected( 0 == f2(x, z) + f2(x, y) + -f2(x, (y + z)) ) })
                })
      .expected(exactly( 
            clause({           0 == x, (y + z) - g2(   f2(x, y) + f2(x, z)   , x) > 0    })  // (1)
          , clause({           0 == x,    z    - g2(f2(x, (y + z)) - f2(x, y), x) > 0  })  // (2)
          , clause({           0 == x,    y    - g2(f2(x, (y + z)) - f2(x, z), x) > 0  })  // (3)
          ))
    )


TEST_GENERATION(bug01b,
    Generation::SymmetricTest()
      .indices(alascaSuperpositionIndices())
      .selfApplications(false)
      .inputs  ({        clause({ selected(  z + -g2((y * z), y) > 0 ), 0 == y  })
                          // (1) {y -> x, z -> y + z}
                          // ==> { (y + z) + -g2((x * (y + z)), x) > 0 , 0 == x }
                          // (2) {y -> x, z -> z}
                          // ==> { z + -g2((x * z), x) > 0 , 0 == x }
                          // (3) {y -> x, z -> y}
                          // ==> { y + -g2((x * y), x) > 0, 0 == x  }

                ,        clause({ selected( 0 == (x * z) + (x * y) + -(x * (y + z)) ) })
                })
      .expected(exactly( 
            clause({           0 == x, (y + z) - g2(   (x * y) + (x * z)   , x) > 0    })  // (1)
          , clause({           0 == x,    z    - g2((x * (y + z)) - (x * y), x) > 0  })  // (2)
          , clause({           0 == x,    y    - g2((x * (y + z)) - (x * z), x) > 0  })  // (3)
          ))
    )

TEST_GENERATION(only_replace_max_rat,
    Generation::SymmetricTest()
      .indices(alascaSuperpositionIndices())
      .selfApplications(false)
      .inputs  ({        clause({ selected( 0 == f(x) + f(y) + x ) })
                ,        clause({ selected( p(f(g(a)))           ) })
                })
      .expected(exactly( 
          clause({  p(-f(y) - g(a)) }) 
        , clause({  p(-f(x) - x) }) 
      ))
    )

TEST_GENERATION(only_replace_max_uninter_01,
    Generation::SymmetricTest()
      .indices(alascaSuperpositionIndices())
      .inputs  ({        clause({ selected( fa(x) == aa   ) })
                ,        clause({ selected( p(fn(fa(f(b))))  ) })
                })
      .expected(exactly( 
          clause({  p(fn(aa)) }) 
      ))
    )


TEST_GENERATION(only_replace_max_uninter_02,
    Generation::SymmetricTest()
      .indices(alascaSuperpositionIndices())
      .selfApplications(false)
      .inputs  ({        clause({ selected( fa(x) == fa(y)   ) })
                ,        clause({ selected( p(fn(fa(f(b))))  ) })
                })
      .expected(exactly( 
          clause({  p(fn(fa(x))) }) 
        , clause({  p(fn(fa(y))) }) 
      ))
    )

TEST_GENERATION(only_replace_by_smaller_uninterp_01,
    Generation::SymmetricTest()
      .indices(alascaSuperpositionIndices())
      .inputs  ({        clause({ selected( ga(x, a) == ga(f(a), x) ) })
                ,        clause({ selected( p(fn(ga(a, a)))         ) })
                })
      .expected(exactly(  /* nothing */ ))
    )

TEST_GENERATION(only_replace_by_smaller_uninterp_02,
    Generation::SymmetricTest()
      .indices(alascaSuperpositionIndices())
      .inputs  ({        clause({ selected( ga(x, a) == ga(f(a), x) ) })
                ,        clause({ selected( p(fn(ga(f(a), a)))      ) })
                }) /////////////////////////////////////////////////////
      .expected(exactly( clause({           p(fn(ga(a, a)))           }) ))
    )

#define for_diamond(macro)                                                                \
  macro(> , gt )                                                                          \
  macro(>=, geq)                                                                          \
  macro(==, eq )                                                                          \
  macro(!=, neq)                                                                          \


#define TEST_only_replace_in_active(diamond, name)                                        \
                                                                                          \
  TEST_GENERATION(only_replace_uninter_in_active__ ## name ## __fail,                     \
      Generation::SymmetricTest()                                                         \
        .indices(alascaSuperpositionIndices())                                               \
        .inputs  ({ clause({ selected( fa(b) == ba )  })                                  \
                  , clause({ selected( f(f(f(a))) + fn(fa(b)) diamond  0 )  }) })         \
        .expected(exactly( /* nothing */)))                                               \
                                                                                          \
  TEST_GENERATION(only_replace_uninter_in_active__ ## name ## __success,                  \
      Generation::SymmetricTest()                                                         \
        .indices(alascaSuperpositionIndices())                                               \
        .inputs  ({ clause({ selected( fa(b) == ba )  })                                  \
                  , clause({ selected( fn(fa(b)) + b diamond  0 )  }) })                  \
        .expected(exactly(                                                                \
              clause({ fn(ba) + b diamond 0 })                                            \
        )))                                                                               \
                                                                                          \
  TEST_GENERATION(only_replace_rat_in_active__ ## name ## __fail,                         \
      Generation::SymmetricTest()                                                         \
        .indices(alascaSuperpositionIndices())                                               \
        .inputs  ({ clause({ selected( f(b) - a == 0 )  })                                \
                  , clause({ selected( f(f(a)) + f(b) diamond  0 )  }) })                 \
        .expected(exactly( /* nothing */)))                                               \
                                                                                          \
  TEST_GENERATION(only_replace_rat_in_active__ ## name ## __success,                      \
      Generation::SymmetricTest()                                                         \
        .indices(alascaSuperpositionIndices())                                               \
        .inputs  ({ clause({ selected( f(b) - a == 0 )  })                                \
                  , clause({ selected( f(f(b)) + a diamond  0 )  }) })                    \
        .expected(exactly(                                                                \
          clause({ f(a) + a diamond 0 })                                                  \
          )))                                                                             \

for_diamond(TEST_only_replace_in_active)

#define for_polarity(macro)                                                               \
  macro( , pos)                                                                           \
  macro(~, neg)                                                                           \


#define TEST_only_replace_in_active_uninterpretd(pol, name)                               \
  TEST_GENERATION(replace_unintepreted_in_active_uninterpreted_ ## name,                  \
      Generation::SymmetricTest()                                                         \
        .indices(alascaSuperpositionIndices())                                               \
        .inputs  ({ clause({ selected( fa(b) == ba ) })                                   \
                  , clause({ selected( pol p(fn(fa(b)))    ) }) })                        \
        .expected(exactly(                                                                \
                    clause({ selected( pol p(fn(ba))    ) })                              \
        )))                                                                               \
                                                                                          \
  TEST_GENERATION(replace_rat_in_active_uninterpreted_ ## name,                           \
      Generation::SymmetricTest()                                                         \
        .indices(alascaSuperpositionIndices())                                               \
        .inputs  ({ clause({ selected( f(b) - a == 0 ) })                                 \
                  , clause({ selected( pol p(f(f(b)))    ) }) })                          \
        .expected(exactly(                                                                \
                    clause({ selected( pol p(f(a))    ) })                                \
        )))                                                                               \

for_polarity(TEST_only_replace_in_active_uninterpretd)

// 17851. 0 = (-400 + uninterp_mul(400,1)) [alasca normalization 17849]
// 17137. 0 = (a + (-b + uninterp_mul((-a + b),1))) [alasca normalization 17135]
// 115090. 0 = (a + (-b + 400)) [alasca superposition 17851,17137]
TEST_GENERATION_WITH_SUGAR(int_bug01, SUGAR(Int),
    Generation::SymmetricTest()
      .indices(alascaSuperpositionIndices())
      .rule(move_to_heap(testSuperposition(Options::UnificationWithAbstraction::ALASCA_MAIN)))
      .inputs  ({ clause({ 0 == (-400 + f2(400,1))  }) 
                , clause({ 0 == (a + (-b + f2((-a + b),1)))  }) 
                })
      .expected(exactly(  ))
    )



#if INT_TESTS
TEST_GENERATION_WITH_SUGAR(int_01, SUGAR(Int),
    Generation::SymmetricTest()
      .indices(alascaSuperpositionIndices())
      .inputs  ({ clause({ selected( 3 * f(x) - a == 0 )  }) 
                , clause({ selected( p(3 * f(a)))  }) })
      .expected(exactly( clause({ p(a)  }) ))
    )

TEST_GENERATION_WITH_SUGAR(int_02, SUGAR(Int),
    Generation::SymmetricTest()
      .indices(alascaSuperpositionIndices())
      .inputs  ({ clause({ selected( 3 * f(x) - a == 0 )  })
                , clause({ selected(     p(f(x)) )  }) })
      .expected(exactly( /* nothing */ ))
    )

TEST_GENERATION_WITH_SUGAR(int_03, SUGAR(Int),
    Generation::SymmetricTest()
      .indices(alascaSuperpositionIndices())
      .inputs  ({ clause({ selected( 3 * f(x) - a == 0 )  })
                , clause({ selected(     p(21 * f(x)) )  }) })
      .expected(exactly( clause({ p(7 * a)  }) ))
    )

#endif // INT_TESTS


TEST_GENERATION(two_var_01,
    Generation::SymmetricTest()
      .indices(alascaSuperpositionIndices())
      .selfApplications(false)
      .inputs  ({ clause({ x == aa   }) 
                , clause({ p(f(a))  }) })
      .expected(exactly(
          /* nothing */
      ))
    )

TEST_GENERATION(bug02,
    Generation::SymmetricTest()
      .indices(alascaSuperpositionIndices())
      .inputs  ({ clause({ x == aa   }) })
      .expected(exactly(
          clause({ sorted(x, alpha) == y })
          /* nothing */
      ))
    )


TEST_GENERATION(bug03,
    Generation::SymmetricTest()
      .indices(alascaSuperpositionIndices())
      .inputs  ({ 
          clause({ pa(aa)   })
        , clause({ x == sorted(y, alpha), fa(x) != fa(y) })
        })
      .expected(exactly(
          /* nothing */
      ))
    )

TEST_GENERATION(bug04,
    Generation::SymmetricTest()
      .indices(alascaSuperpositionIndices())
      .inputs  ({ 
          clause({ p(a)   })
        , clause({ 0  == x - y, 0 != f(x) - f(y) })
        })
      .expected(exactly(
          /* nothing */
      ))
    )

TEST_GENERATION(bug05,
    Generation::SymmetricTest()
      .indices(alascaSuperpositionIndices())
      .selfApplications(true)
      .inputs  ({ 
          clause({ x == true, x == false   })
        })
      .expected(exactly(
          /* nothing */
      ))
    )
 
  //   ;- unit id: 655
  // (assert (or false
  //   (= (/ 0.0 1.0) (+ (-(/ 8.0 1.0)) (- a)))
  //   ))
  //
  // ;- unit id: 7201
  // (assert (forall ((x2 Real)(x6 Real)(x4 Real)(x0 Real)(x3 Real)(x5 Real)(x1 Real))(or false
  //   (>= (+ (/ 3.0 1.0) (+ (* (-(/ 6.0 1.0)) x1) (+ (- (* c2 x5)) (+ (- (* c4 x0)) (* (-(/ 15.0 1.0)) (sK208 x0 x3 x4 x1)))))) (/ 0.0 1.0))
  //   (>= (+ b (+ (* (-(/ 7.0 1.0)) x0) (+ (* (-(/ 15.0 1.0)) x6) (- (* c1 (sK208 x0 x3 x4 x1)))))) (/ 0.0 1.0))
  //   (>= (+ c (+ (- (* c x3)) (+ (- (* f(b) x6)) (+ (* (-(/ 4.0 1.0)) (sK208 x0 x3 x4 x1)) (- (* a x2)))))) (/ 0.0 1.0))
  //   )))
  //
  //
  // ;- rule: alasca superposition
  //
  // ;- unit id: 7316
  // (assert (not (forall ((x5 Real)(x6 Real)(x4 Real)(x0 Real)(x3 Real)(x2 Real)(x1 Real))(or false
  //   (>= (+ (/ 10.0 1.0) (+ (* (-(/ 13.0 1.0)) x0) (+ (* (-(/ 10.0 1.0)) y4) (+ (- (* c3 y5)) (* (-(/ 17.0 1.0)) (sK209 y2 y0 y3 y4)))))) (/ 0.0 1.0))
  //   (>= (+ (/ 3.0 1.0) (+ (* (-(/ 6.0 1.0)) y4) (+ (- (* c2 y6)) (+ (- (* c4 y2)) (* (-(/ 15.0 1.0)) (sK208 y2 y0 y3 y4)))))) (/ 0.0 1.0))
  //   (>= (+ b (+ (* (-(/ 7.0 1.0)) y2) (+ (* (-(/ 15.0 1.0)) y1) (- (* c1 (sK208 y2 y0 y3 y4)))))) (/ 0.0 1.0))
  //   (>= (+ c (+ (- (* c y0)) (+ (- (* f(b) y1)) (+ (* (-(/ 4.0 1.0)) (sK208 y2 y0 y3 y4)) (- (* (-(/ 8.0 1.0)) y5)))))) (/ 0.0 1.0))
  //   ))))
  // (check-sat)

TEST_GENERATION(bug06,
    Generation::SymmetricTest()
      .indices(alascaSuperpositionIndices())
      .selfApplications(true)
      .inputs  ({ 
          clause({ 0 == -8 + -a  }),
          clause({
    10 + -13 * x0 + -10 * x1 + -(c3 * x2) -17 * f4(x0, x3, x4, x1) >= 0,
    3 + -6 * x1 + -(c2 * x5) -(c4 * x0) + -15 * g4(x0,x3,x4,x1) >= 0,
    b + (-7 * x0) + (-15 * x6) + -(c1 * g4(x0,x3,x4,x1)) >= 0,
    c +  -(c * x3) + -(f(b) * x6) + (-4 * g4(x0,x3,x4,x1)) - (a * x2) >= 0,
              })

        })
      .expected(exactly(
          clause({
    10 + -13 * x0 + -10 * x1 + -(c3 * x2) -17 * f4(x0, x3, x4, x1) >= 0,
    3 + -6 * x1 + -(c2 * x5) -(c4 * x0) + -15 * g4(x0,x3,x4,x1) >= 0,
    b + (-7 * x0) + (-15 * x6) + -(c1 * g4(x0,x3,x4,x1)) >= 0,
    c +  -(c * x3) + -(f(b) * x6) + (-4 * g4(x0,x3,x4,x1)) - (-8 * x2) >= 0,
              })
      ))
    )

TEST_GENERATION(abstraction_bug01a,
    Generation::SymmetricTest()
      .indices(alascaSuperpositionIndices())
      .rule(move_to_heap(testSuperposition(Options::UnificationWithAbstraction::ALASCA_MAIN)))
      .selfApplications(false)
      .inputs  ({ 
          clause({ 0 == f2(f(x), 0)  }),
          clause({ 0 == f2(a, x) + -f2(a, -x + b) })
        })
      .expected(exactly(
          // nothing
      ))
    )
 
TEST_GENERATION(abstraction_bug01b,
    Generation::SymmetricTest()
      .indices(alascaSuperpositionIndices())
      .rule(move_to_heap(testSuperposition(Options::UnificationWithAbstraction::ALASCA_MAIN)))
      .selfApplications(false)
      .inputs  ({ 
          clause({ 0 == f2(f(x), 0)  }),
          clause({ 0 == f2(a, x) + -f2(a, -x + b) })
        })
      .expected(exactly(
          // nothing
      ))
    )
 
 
TEST_GENERATION(is_int_skip_app,
    Generation::SymmetricTest()
      .indices(alascaSuperpositionIndices())
      .rule(move_to_heap(testSuperposition(Options::UnificationWithAbstraction::ALASCA_MAIN_FLOOR)))
      .selfApplications(true)
      .inputs  ({ 
          clause({ f(x) == floor(f(x))  }),
        })
      .expected(exactly(
          // nothing
      ))
    )
 

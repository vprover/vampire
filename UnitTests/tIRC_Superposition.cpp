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
#include "Inferences/IRC/Superposition.hpp"
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
using namespace Inferences::IRC;

///////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// TEST CASES 
/////////////////////////////////////

#define SUGAR(Num)                                                                                  \
  NUMBER_SUGAR(Num)                                                                                 \
  DECL_DEFAULT_VARS                                                                                 \
  DECL_FUNC(f, {Num}, Num)                                                                          \
  DECL_FUNC(g, {Num}, Num)                                                                          \
  DECL_FUNC(f2, {Num, Num}, Num)                                                                    \
  DECL_FUNC(g2, {Num, Num}, Num)                                                                    \
  DECL_CONST(a, Num)                                                                                \
  DECL_CONST(b, Num)                                                                                \
  DECL_CONST(c, Num)                                                                                \
  DECL_PRED(p, {Num})                                                                               \
  DECL_PRED(r, {Num,Num})                                                                           \
                                                                                                    \
  DECL_SORT(alpha)                                                                                  \
  DECL_FUNC(fa, {Num}, alpha)                                                                       \
  DECL_FUNC(ga, {Num, Num}, alpha)                                                                  \
  DECL_CONST(aa, alpha)                                                                             \
  DECL_CONST(ba, alpha)                                                                             \
  DECL_FUNC(fn, {alpha}, Num)                                                                       \

#define MY_SYNTAX_SUGAR SUGAR(Rat)

#define UWA_MODE Options::UnificationWithAbstraction::IRC1

Stack<std::function<Indexing::Index*()>> ircSuperpositionIndices()
{ return {
    [](){ return new IrcIndex<Superposition::Lhs>(UWA_MODE);},
    [](){ return new IrcIndex<Superposition::Rhs>(UWA_MODE);},
    // [](){ return new Indexing::IRCSuperpositionLhsIndex(new TermSubstitutionTree(UWA_MODE, true));},
    // [](){ return new Indexing::IRCSuperpositionRhsIndex(new TermSubstitutionTree(UWA_MODE, true));},
  }; }

Superposition testSuperposition()
{ return Superposition(testIrcState(UWA_MODE)); }



REGISTER_GEN_TESTER(Test::Generation::GenerationTester<Superposition>(testSuperposition()))

/////////////////////////////////////////////////////////
// Basic tests
//////////////////////////////////////

TEST_GENERATION(basic01,
    Generation::SymmetricTest()
      .indices(ircSuperpositionIndices())
      .inputs  ({ clause({ selected( 3 * f(x) - 4 == 0 )  }) 
                , clause({ selected(     3 * f(x) >  0 )  }) })
      .expected(exactly(
            clause({ 3 * frac(4,3) > 0  })
      ))
    )

TEST_GENERATION(basic02,
    Generation::SymmetricTest()
      .indices(ircSuperpositionIndices())
      .inputs  ({ clause({ selected( 3 * f(x) - 4 == 0 )  })
                , clause({ selected(     f(x) >  0 )  }) })
      .expected(exactly(
            clause({ frac(4, 3) > 0  })
      ))
    )

TEST_GENERATION(basic03,
    Generation::SymmetricTest()
      .indices(ircSuperpositionIndices())
      .inputs  ({ clause({selected( f(a) + a + 3 == 0 ) })
                , clause({selected( f(x) > 0 ) }) })
      .expected(exactly(
            clause({ - a + -3 > 0  })
      ))
    )

TEST_GENERATION(basic04,
    Generation::SymmetricTest()
      .indices(ircSuperpositionIndices())
      .inputs  ({ clause({ selected( f(a) + a + 3 == 0 ) })
                , clause({  f(x) > 0, selected(f(g(x)) > 0) }) })
      .expected(exactly(
      ))
    )

TEST_GENERATION(basic05,
    Generation::SymmetricTest()
      .indices(ircSuperpositionIndices())
      .inputs  ({ clause({selected( f(a) + a + 3 == 0 ) })
                , clause({selected( p(f(x)) ) }) })
      .expected(exactly(
            clause({ p(- a + -3)  })
      ))
    )

TEST_GENERATION(basic06,
    Generation::SymmetricTest()
      .indices(ircSuperpositionIndices())
      .inputs  ({ clause({selected( f(a) + a + 3 == 0 ) })
                , clause({selected( g(f(x)) != 0 ) }) })
      .expected(exactly(
            clause({ g(-a + -3) != 0 })
      ))
    )

TEST_GENERATION(basic07,
    Generation::SymmetricTest()
      .indices(ircSuperpositionIndices())
      .inputs  ({ clause({selected( f(a) + a + 3 == 0 ) })
                , clause({selected( g(3 * f(x)) != 0 ) }) })
      .expected(exactly(
            clause({ g(3 * (-a + -3)) != 0 })
      ))
    )

// • s2σ ⊴ t ∈ active(L[s2]σ)
TEST_GENERATION(basic10,
    Generation::SymmetricTest()
      .indices(ircSuperpositionIndices())
      .inputs  ({ clause({selected( g2(x, y) + g2(y, y) > 0 ) })
                , clause({selected( g2(a, f(a)) - a == 0 ) }) })
      .expected(exactly(
            // clause({ g(3 * (-a + -3)) != 0 })
          /* nothing */
      ))
    )

TEST_GENERATION(uwa1,
    Generation::SymmetricTest()
      .indices(ircSuperpositionIndices())
      .inputs  ({ clause({ selected( f(a + b) == 0 )  })
                , clause({ selected(   a - b  == 0 )  }) })
      .expected(exactly(
            clause({ f(a + a) == 0  })
      ))
    )


TEST_GENERATION(misc01,
    Generation::SymmetricTest()
      .indices(ircSuperpositionIndices())
      .inputs  ({         clause({ selected(0 == -17 + a) })
                ,         clause({ selected(-19 + -f(x) + a * y  >= 0) }) })
      .expected(exactly(  clause({          -19 + -f(x) + 17 * y >= 0  }) ))
    )

// •    L[s2]σ  ∈ Lit+ and L[s2]σ /⪯ C2σ
//   or L[s2]σ /∈ Lit+ and L[s2]σ /≺ C2σ
TEST_GENERATION(ordering1_ok_1,
    Generation::SymmetricTest()
      .indices(ircSuperpositionIndices())
      .inputs  ({         clause({ selected( g2(a,a) == 0 ) })
                ,         clause({ selected( f(g2(x,y)) != 0 ), selected( f(g2(y,x)) != 0 ) }) }) 
      .expected(exactly(  clause({ f(0) != 0, f(g2(a,a)) != 0 }) 
                       ,  clause({ f(0) != 0, f(g2(a,a)) != 0 }) ))
    )
TEST_GENERATION(ordering1_ok_2,
    Generation::SymmetricTest()
      .indices(ircSuperpositionIndices())
      .inputs  ({         clause({ selected( g2(a,a) == 0 ) })
                ,         clause({ selected( -f(g2(x,y)) > 0 ), selected( -f(g2(y,x)) > 0 ) }) }) 
      .expected(exactly(  clause({ -f(0) > 0, -f(g2(a,a)) > 0 }) 
                       ,  clause({ -f(0) > 0, -f(g2(a,a)) > 0 }) ))
    )
TEST_GENERATION(ordering1_fail_1,
    Generation::SymmetricTest()
      .indices(ircSuperpositionIndices())
      .inputs  ({         clause({ selected( g2(a,a) == 0 ) })
                ,         clause({ selected( f(g2(x,y)) > 0 ), selected( f(g2(y,x)) > 0 ) }) }) 
      .expected(exactly(  /* */ ))
    )
// TEST_GENERATION(ordering1_fail_2,
//     Generation::SymmetricTest()
//       .indices(ircSuperpositionIndices())
//       .inputs  ({         clause({ g2(a,a) == 0 })
//                 ,         clause({ -f(g2(x,y)) > 0, -f(g2(y,x)) > 0 }) }) 
//       .expected(exactly(  /* nothing */          ))
//     )

// • (±k. s1 + t1 ≈ 0)σ is strictly maximal in Hyp1σ
TEST_GENERATION(ordering2_ok,
    Generation::SymmetricTest()
      .indices(ircSuperpositionIndices())
      .inputs  ({         clause({ selected( g2(x,y) == 0 ), selected( g2(z,z) == 0 ) })
                ,         clause({ selected( f(g2(a,a)) > 0 ) }) }) 
      .expected(exactly(  clause({ f(0) > 0, g2(x,x) == 0 }) 
                       ,  clause({ f(0) > 0, g2(x,y) == 0 }) ))
    )
TEST_GENERATION(ordering2_fail,
    Generation::SymmetricTest()
      .indices(ircSuperpositionIndices())
      .inputs  ({         clause({ g2(x,y) == 0, g2(y,x) == 0 })
                ,         clause({ f(g2(a,a)) > 0 }) }) 
      .expected(exactly(  /* nothing */  ))
    )

// •        s1  σ is strictly maximal in terms(s1 + t1)σ
TEST_GENERATION(ordering3_ok,
    Generation::SymmetricTest()
      .indices(ircSuperpositionIndices())
      .inputs  ({         clause({ selected( g2(x,y) + g2(z,z) + g2(z,z) == 0 ) })
                ,         clause({ selected( f(g2(a,a)) > 0                   ) }) }) 
      .expected(exactly(  clause({ f(       -2  * g2(z,z)) > 0 }) 
                       ,  clause({ f(frac(-1,2) * g2(x,y)) > 0 }) ))
    )
TEST_GENERATION(ordering3_fail,
    Generation::SymmetricTest()
      .indices(ircSuperpositionIndices())
      .inputs  ({         clause({  g2(x,y) + g2(y,x) + g2(y,x) == 0 })
                ,         clause({ f(g2(a,a)) > 0 }) }) 
      .expected(exactly(  /* nothing */  ))
    )


TEST_GENERATION(uninterpreted_pred_1,
    Generation::SymmetricTest()
      .indices(ircSuperpositionIndices())
      .inputs  ({        clause({ selected(   f(x) - 1 == 0 )  })
                ,        clause({ selected( p(f(x)) )          }) })
      .expected(exactly( clause({           p(1)               })
      ))
    )

TEST_GENERATION(uninterpreted_pred_2,
    Generation::SymmetricTest()
      .indices(ircSuperpositionIndices())
      .inputs  ({        clause({ selected(   f(x) - 1 == 0 )      })
                ,        clause({ selected( p(f(a)) ), f(f(b)) > 0 }) })
      .expected(exactly( clause({           p(1)     , f(f(b)) > 0 }) ))
    )

TEST_GENERATION(uninterpreted_pred_3, // TODO couldn't we replace all occurences of f(x) instead of the maximal one
    Generation::SymmetricTest()
      .indices(ircSuperpositionIndices())
      .inputs  ({        clause({ selected(   f(x) - 1 == 0 )      })
                ,        clause({ selected( p(f(x)) ), f(f(x)) > 0 }) })
      .expected(exactly( clause({           p(1)     , f(f(x)) > 0 }) ))
    )

TEST_GENERATION(uninterpreted_sort_1,
    Generation::SymmetricTest()
      .indices(ircSuperpositionIndices())
      .inputs  ({        clause({ selected( f(x) - 1 == 0  ) })
                ,        clause({ selected( fa(f(x)) == aa ) }) })
      .expected(exactly( clause({           fa(  1 ) == aa   }) ))
    )

TEST_GENERATION(uninterpreted_sort_2,
    Generation::SymmetricTest()
      .indices(ircSuperpositionIndices())
      .inputs  ({        clause({ selected( f(x) - 1 == 0  ) })
                ,        clause({ selected( fa(3 *   f(x)) == aa ) }) })
      .expected(exactly( clause({           fa(3 * num(1)) == aa   }) ))
    )

// 0.0 = $sum(X2,$uminus($quotient($product(X1,X2),X1))) | 0.0 = X1 [theory normalization 6]
// 0.0 = $sum($product(X0,X2),$sum($product(X0,X1),$uminus($product(X0,$sum(X1,X2))))) [theory normalization 3]



TEST_GENERATION(bug01a,
    Generation::SymmetricTest()
      .indices(ircSuperpositionIndices())
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
      .indices(ircSuperpositionIndices())
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
      .indices(ircSuperpositionIndices())
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
      .indices(ircSuperpositionIndices())
      .inputs  ({        clause({ selected( fa(x) == aa   ) })
                ,        clause({ selected( p(fn(fa(f(b))))  ) })
                })
      .expected(exactly( 
          clause({  p(fn(aa)) }) 
      ))
    )


TEST_GENERATION(only_replace_max_uninter_02,
    Generation::SymmetricTest()
      .indices(ircSuperpositionIndices())
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
      .indices(ircSuperpositionIndices())
      .inputs  ({        clause({ selected( ga(x, a) == ga(f(a), x) ) })
                ,        clause({ selected( p(fn(ga(a, a)))         ) })
                })
      .expected(exactly(  /* nothing */ ))
    )

TEST_GENERATION(only_replace_by_smaller_uninterp_02,
    Generation::SymmetricTest()
      .indices(ircSuperpositionIndices())
      .inputs  ({        clause({ selected( ga(x, a) == ga(f(a), x) ) })
                ,        clause({ selected( p(fn(ga(f(a), a)))      ) })
                }) /////////////////////////////////////////////////////
      .expected(exactly( clause({           p(fn(ga(a, a)))           }) ))
    )

#define for_diamond(macro)                                                                          \
  macro(> , gt )                                                                                    \
  macro(>=, geq)                                                                                    \
  macro(==, eq )                                                                                    \
  macro(!=, neq)                                                                                    \


#define TEST_only_replace_in_active(diamond, name)                                                  \
                                                                                                    \
  TEST_GENERATION(only_replace_uninter_in_active__ ## name ## __fail,                        \
      Generation::SymmetricTest()                                                                   \
        .indices(ircSuperpositionIndices())                                                         \
        .inputs  ({ clause({ selected( fa(b) == ba )  })                                            \
                  , clause({ selected( f(f(f(a))) + fn(fa(b)) diamond  0 )  }) })                   \
        .expected(exactly( /* nothing */)))                                                         \
                                                                                                    \
  TEST_GENERATION(only_replace_uninter_in_active__ ## name ## __success,                     \
      Generation::SymmetricTest()                                                                   \
        .indices(ircSuperpositionIndices())                                                         \
        .inputs  ({ clause({ selected( fa(b) == ba )  })                                            \
                  , clause({ selected( fn(fa(b)) + b diamond  0 )  }) })                            \
        .expected(exactly(                                                                          \
              clause({ fn(ba) + b diamond 0 })                                                      \
        )))                                                                                         \
                                                                                                    \
  TEST_GENERATION(only_replace_rat_in_active__ ## name ## __fail,                            \
      Generation::SymmetricTest()                                                                   \
        .indices(ircSuperpositionIndices())                                                         \
        .inputs  ({ clause({ selected( f(b) - a == 0 )  })                                          \
                  , clause({ selected( f(f(a)) + f(b) diamond  0 )  }) })                           \
        .expected(exactly( /* nothing */)))                                                         \
                                                                                                    \
  TEST_GENERATION(only_replace_rat_in_active__ ## name ## __success,                         \
      Generation::SymmetricTest()                                                                   \
        .indices(ircSuperpositionIndices())                                                         \
        .inputs  ({ clause({ selected( f(b) - a == 0 )  })                                          \
                  , clause({ selected( f(f(b)) + a diamond  0 )  }) })                              \
        .expected(exactly(                                                                          \
          clause({ f(a) + a diamond 0 })                                                            \
          )))                                                                                       \

for_diamond(TEST_only_replace_in_active)

#define for_polarity(macro)                                                                         \
  macro( , pos)                                                                                     \
  macro(~, neg)                                                                                     \


#define TEST_only_replace_in_active_uninterpretd(pol, name)                                         \
  TEST_GENERATION(replace_unintepreted_in_active_uninterpreted_ ## name,                     \
      Generation::SymmetricTest()                                                                   \
        .indices(ircSuperpositionIndices())                                                         \
        .inputs  ({ clause({ selected( fa(b) == ba ) })                                             \
                  , clause({ selected( pol p(fn(fa(b)))    ) }) })                                  \
        .expected(exactly(                                                                          \
                    clause({ selected( pol p(fn(ba))    ) })                                        \
        )))                                                                                         \
                                                                                                    \
  TEST_GENERATION(replace_rat_in_active_uninterpreted_ ## name,                              \
      Generation::SymmetricTest()                                                                   \
        .indices(ircSuperpositionIndices())                                                         \
        .inputs  ({ clause({ selected( f(b) - a == 0 ) })                                           \
                  , clause({ selected( pol p(f(f(b)))    ) }) })                                    \
        .expected(exactly(                                                                          \
                    clause({ selected( pol p(f(a))    ) })                                          \
        )))                                                                                         \

for_polarity(TEST_only_replace_in_active_uninterpretd)

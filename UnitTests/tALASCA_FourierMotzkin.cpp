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
#include "Lib/STL.hpp"
#include "Inferences/ALASCA/FourierMotzkin.hpp"

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

// #define BOT num(0) > 0,
#define BOT 

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

#define MY_SYNTAX_SUGAR SUGAR(Rat)

auto idxFourierMotzkin(
    ) { 
  return Generation::TestIndices{
    [=](const SaturationAlgorithm&) { return new AlascaIndex<FourierMotzkin::Lhs>(); },
    [=](const SaturationAlgorithm&) { return new AlascaIndex<FourierMotzkin::Rhs>(); },
  }; 
}

auto testFourierMotzkin(
   Options::UnificationWithAbstraction uwa = Options::UnificationWithAbstraction::ALASCA_MAIN
    ) 
{ 
  auto s = testAlascaState(uwa);
  return alascaSimplRule(s,FourierMotzkin(s), ALASCA::Normalization(s));
}


REGISTER_GEN_TESTER(AlascaGenerationTester<FourierMotzkin>())

/////////////////////////////////////////////////////////
// Basic tests
//////////////////////////////////////

// check whether we apply the rule for every weakly maximal negative term
TEST_GENERATION(basic01,
    Generation::SymmetricTest()
      .indices(idxFourierMotzkin())
      .inputs  ({ clause({selected( 5 * f(x) +       a  > 0 )   }) 
               ,  clause({selected(-2 * f(x) - 3 * f(y) > 0 ) }) })
      .expected(exactly(
            clause({  2 * a + 5 * (-3 * f(y)) > 0  })
          , clause({  3 * a + 5 * (-2 * f(x)) > 0  })
      ))
    )

// check whether we apply the rule only for strictly maximal positive
TEST_GENERATION(basic02,
    Generation::SymmetricTest()
      .indices(idxFourierMotzkin())
      .inputs  ({ clause({selected( 5 * f(x) + 2 * f(f(a)) + a > 0 )   }) 
               ,  clause({selected(-2 * f(a) - 3 * f(a) > 0 ) }) })
      .expected(exactly(
      ))
    )

// inequaity symbols right
TEST_GENERATION(basic0301,
    Generation::SymmetricTest()
      .indices(idxFourierMotzkin())
      .inputs  ({ clause({selected(  f(a) + a > 0 )   }) 
               ,  clause({selected( -f(x) + c > 0 ) }) })
      .expected(exactly(
        clause({ a + c > 0 })
      ))
    )
TEST_GENERATION(basic0302,
    Generation::SymmetricTest()
      .indices(idxFourierMotzkin())
      .inputs  ({ clause({selected(  f(a) + a >= 0 )   }) 
               ,  clause({selected( -f(x) + c > 0 ) }) })
      .expected(exactly(
        clause({ a + c > 0 })
      ))
    )
TEST_GENERATION(basic0303,
    Generation::SymmetricTest()
      .indices(idxFourierMotzkin())
      .inputs  ({ clause({selected(  f(a) + a > 0 )   }) 
               ,  clause({selected( -f(x) + c >= 0 ) }) })
      .expected(exactly(
        clause({ a + c > 0 })
      ))
    )
TEST_GENERATION(basic0304,
    Generation::SymmetricTest()
      .indices(idxFourierMotzkin())
      .inputs  ({ clause({selected(  f(a) + a >= 0 )   }) 
               ,  clause({selected( -f(x) + c >= 0 ) }) })
      .expected(exactly(
        clause({ a + c > 0, -f(a) + c == 0 })
      ))
    )


TEST_GENERATION(basic04,
    Generation::SymmetricTest()
      .indices(idxFourierMotzkin())
      .inputs  ({ clause({selected( f(x) > 0 ), x - 7 == 0   }) 
               ,  clause({selected(-f(x) > 0 )           }) })
      .expected(exactly(
            clause({ BOT  x - 7 == 0  })
      ))
    )

TEST_GENERATION(basic05,
    Generation::SymmetricTest()
      .indices(idxFourierMotzkin())
      .inputs  ({ clause({selected(     f(a) > 0) }) 
               ,  clause({selected(a + -f(a) > 0) }) })
      .expected(exactly(
            clause({  a > 0  })
      ))
    )

TEST_GENERATION(basic06a,
    Generation::SymmetricTest()
      .indices(idxFourierMotzkin())
      .inputs  ({ clause({selected( -g(x,a) + -g(g(a,b), f(x)) > 0) }) 
               ,  clause({selected(  g(a,a) +  g(g(a,b), f(b)) > 0) }) })
      .expected(exactly(
            clause({  g(a,a) + -g(b,a)  > 0  })
      ))
    )

TEST_GENERATION(basic07,
    Generation::SymmetricTest()
      .indices(idxFourierMotzkin())
      .inputs  ({ clause({ selected( a + -f(x) > 0), x - 7 == 0 })  
               ,  clause({ selected( a +  f(a) > 0) })         })
      .expected(exactly(
            clause({  a - 7 == 0, a + a > 0   })
      ))
    )

TEST_GENERATION(basic07_variation,
    Generation::SymmetricTest()
      .indices(idxFourierMotzkin())
      .inputs  ({ clause({ selected( a +  f(a) > 0) })
               ,  clause({ selected( a + -f(x) > 0), x -7 == 0 }) })
      .expected(exactly(
            clause({  a + a > 0, a - 7 == 0  })
      ))
    )

TEST_GENERATION(basic10,
    Generation::SymmetricTest()
      .indices(idxFourierMotzkin())
      .inputs  ({ clause({ selected( a + -f(y) > 0) }) 
               ,  clause({ selected( a +  f(a) > 0), x - 7 == 0 }) })
      .expected(exactly(
            clause({  a + a > 0, x - 7 == 0  })
      ))
    )

TEST_GENERATION(basic12,
    Generation::SymmetricTest()
      .indices(idxFourierMotzkin())
      .inputs  ({ clause({ selected(a > 0) }) 
               ,  clause({ selected(a > 0) }) })
      .expected(exactly(
      ))
    )

TEST_GENERATION(basic14,
    Generation::SymmetricTest()
      .indices(idxFourierMotzkin())
      .inputs  ({ clause({ selected(-a > 0) }) 
               ,  clause({ selected( a > 0) }) })
      .expected(exactly(
          clause({ BOT })
      ))
    )

// Testing only strictly maximal atoms are being chained
TEST_GENERATION(basic15a,
    Generation::SymmetricTest()
      .indices(idxFourierMotzkin())
      .inputs  ({ clause({ selected(- g(x,y) - g(y,x) > 0) }) 
               ,  clause({ selected(  g(x,x) > 0) }) })
      .expected(exactly( /* nothing */ ))
    )

// Testing only strictly maximal atoms are being chained
TEST_GENERATION(basic15b,
    Generation::SymmetricTest()
      .indices(idxFourierMotzkin())
      .inputs  ({ clause({ selected(  g(x,y) + g(y,x) > 0) }) 
               ,  clause({ selected(- g(x,x) > 0) }) })
      .expected(exactly( /* nothing */))
    )

// Testing only strictly maximal atoms are being chained
TEST_GENERATION(basic15c,
    Generation::SymmetricTest()
      .indices(idxFourierMotzkin())
      .inputs         ({ clause({ selected(  g(x,y) > 0) }) 
                      ,  clause({ selected(- g(x,x) > 0) }) })
      .expected(exactly( clause({            BOT  }) ))
    )

// Testing that the rhs may be only weakly not only strictly maximal
TEST_GENERATION(basic16a,
    Generation::SymmetricTest()
      .indices(idxFourierMotzkin())
      .inputs         ({ clause({ - g(x,y) + f(z) > 0, -g(y, x) + f(z) > 0 }) 
                       , clause({ g(x,x) > 0   }) })
      .expected(exactly( clause({ f(z) > 0, - g(x,x) + f(z) > 0   }) 
                       , clause({ f(z) > 0, - g(x,x) + f(z) > 0   }) 
          ))
    )
TEST_GENERATION(basic16b,
    Generation::SymmetricTest()
      .indices(idxFourierMotzkin())
      .inputs         ({ clause({ -g(x,y) + f(x) > 0, -g(y,x) + f(z) > 0 }) 
                       , clause({ g(x,x) > 0   }) })
      .expected(exactly( clause({ f(x) > 0, -g(x,x) + f(z) > 0   }) 
                       , clause({ f(z) > 0, -g(x,x) + f(x) > 0   }) 
          ))
    )

// Testing that the lhs may be only strictly maximal
TEST_GENERATION(basic17a,
    Generation::SymmetricTest()
      .indices(idxFourierMotzkin())
      .inputs         ({ clause({ g(x,y) + f(z) > 0, g(y, x) + f(z) > 0 }) 
                       , clause({ -g(x,x) > 0   }) })
      .expected(exactly( /* nothing */ ))
    )
TEST_GENERATION(basic17b,
    Generation::SymmetricTest()
      .indices(idxFourierMotzkin())
      .inputs         ({ clause({ g(x,y) + f(x) > 0, g(y, x) + f(z) > 0 }) 
                       , clause({ -g(x,x) > 0   }) })
      .expected(exactly( clause({ f(x) > 0, g(x,x) + f(z) > 0   }) 
                       , clause({ f(z) > 0, g(x,x) + f(x) > 0   }) 
          ))
    )

TEST_GENERATION(basic18,
    Generation::SymmetricTest()
      .indices(idxFourierMotzkin())
      .inputs  ({ clause({ b  + a >= 0   }) 
               ,  clause({ -b - a >= 0   }) })
      .expected(exactly( 
          clause({ -a + a > 0, 0 == -a + -b })))
    )

TEST_GENERATION(uwa01_one_interp,
    Generation::SymmetricTest()
      .rule(    move_to_heap(testFourierMotzkin(Shell::Options::UnificationWithAbstraction::ALASCA_ONE_INTERP))  )
      .indices(idxFourierMotzkin())
      .inputs         ({ clause({ -f(a + b) > 0, }) 
                       , clause({  f(x + 1) > 0  }) })
      .expected(exactly( clause({ BOT x + 1 != a + b }) ))
    )

TEST_GENERATION(uwa01,
    Generation::SymmetricTest()
      .rule(    move_to_heap(testFourierMotzkin(Shell::Options::UnificationWithAbstraction::ALASCA_MAIN))  )
      .indices(idxFourierMotzkin())
      .inputs         ({ clause({ -f(a + b) > 0, }) 
                       , clause({  f(x + 1) > 0  }) })
      .expected(exactly( clause({ BOT  }) ))
    )

TEST_GENERATION(uwa02,
    Generation::SymmetricTest()
      .rule(    move_to_heap(testFourierMotzkin(Shell::Options::UnificationWithAbstraction::ALASCA_MAIN))  )
      .indices(idxFourierMotzkin())
      .inputs         ({ clause({ -f(a + b) > 0, }) 
                       , clause({  f(a + 1) > 0  }) })
      .expected(exactly( /* nothing */ ))
    )

TEST_GENERATION(uwa03,
    Generation::SymmetricTest()
      .rule(    move_to_heap(testFourierMotzkin(Shell::Options::UnificationWithAbstraction::ALASCA_MAIN))  )
      .indices(idxFourierMotzkin())
      .inputs         ({ clause({ -f(f(x) + b) > 0, }) 
                       , clause({  f(f(y) + 1) > 0  }) })
      .expected(exactly( /* nothing */ ))
    )

TEST_GENERATION(uwa04,
    Generation::SymmetricTest()
      .rule(    move_to_heap(testFourierMotzkin(Shell::Options::UnificationWithAbstraction::ALASCA_CAN_ABSTRACT))  )
      .indices(idxFourierMotzkin())
      .inputs         ({ clause({ -f(f(x) + b) > 0, }) 
                       , clause({  f(f(y) + b) > 0  }) })
      .expected(exactly( clause({ BOT f(x) + b != f(y) + b }) ))
    )

TEST_GENERATION(uwa05,
    Generation::SymmetricTest()
      .rule(    move_to_heap(testFourierMotzkin(Shell::Options::UnificationWithAbstraction::ALASCA_MAIN))  )
      .indices(idxFourierMotzkin())
      .inputs         ({ clause({ -f(f(x) + b) > 0, }) 
                       , clause({  f(f(y) + b + a) > 0  }) })
      .expected(exactly( /* nothing */ ))
    )

TEST_GENERATION(uwa06,
    Generation::SymmetricTest()
      .rule(    move_to_heap(testFourierMotzkin(Shell::Options::UnificationWithAbstraction::ALASCA_MAIN))  )
      .indices(idxFourierMotzkin())
      .inputs         ({ clause({ -f(f(x) + b + a) > 0, }) 
                       , clause({  f(f(y) + b) > 0  }) })
      .expected(exactly( /* nothing */ ))
    )

TEST_GENERATION(uwa07,
    Generation::SymmetricTest()
      .rule(    move_to_heap(testFourierMotzkin(Shell::Options::UnificationWithAbstraction::ALASCA_MAIN))  )
      .indices(idxFourierMotzkin())
      .inputs         ({ clause({ -f(f(x) + 2 * b) > 0, }) 
                       , clause({  f(f(y) + b) > 0  }) })
      .expected(exactly( /* nothing */ ))
    )

TEST_GENERATION(uwa08,
    Generation::SymmetricTest()
      .rule(    move_to_heap(testFourierMotzkin(Shell::Options::UnificationWithAbstraction::ALASCA_MAIN))  )
      .indices(idxFourierMotzkin())
      .inputs         ({ clause({ -f(f(x) - b) > 0, }) 
                       , clause({  f(f(y) + b) > 0  }) })
      .expected(exactly( /* nothing */ ))
    )

TEST_GENERATION(uwa09,
    Generation::SymmetricTest()
      .rule(    move_to_heap(testFourierMotzkin(Shell::Options::UnificationWithAbstraction::ALASCA_MAIN))  )
      .indices(idxFourierMotzkin())
      .inputs         ({ clause({ -f(f(x) - b) > 0, }) 
                       , clause({  f(f(y) + b - z) > 0  }) })
      .expected(exactly( clause({ BOT }) ))
    )

TEST_GENERATION(uwa09_one_interp,
    Generation::SymmetricTest()
      .rule(    move_to_heap(testFourierMotzkin(Shell::Options::UnificationWithAbstraction::ALASCA_ONE_INTERP))  )
      .indices(idxFourierMotzkin())
      .inputs         ({ clause({ -f(f(x) - b) > 0, }) 
                       , clause({  f(f(y) + b - z) > 0  }) })
      .expected(exactly( clause({ BOT f(x) - b != f(z) + b - y }) ))
    )

TEST_GENERATION(uwa10,
    Generation::SymmetricTest()
      .rule(    move_to_heap(testFourierMotzkin(Shell::Options::UnificationWithAbstraction::ALASCA_MAIN))  )
      .indices(idxFourierMotzkin())
      .inputs         ({ clause({ -f(f(x) - b) > 0, }) 
                       , clause({  f(f(y) + b - z) > 0  }) })
      .expected(exactly( clause({ BOT }) ))
    )

TEST_GENERATION(uwa10_one_interp,
    Generation::SymmetricTest()
      .rule(    move_to_heap(testFourierMotzkin(Shell::Options::UnificationWithAbstraction::ALASCA_ONE_INTERP))  )
      .indices(idxFourierMotzkin())
      .inputs         ({ clause({ -f(f(x) - b) > 0, }) 
                       , clause({  f(f(y) + b - z) > 0  }) })
      .expected(exactly( clause({ BOT f(x) - b != f(y) + b - z }) ))
    )

TEST_GENERATION(uwa11,
    Generation::SymmetricTest()
      .rule(    move_to_heap(testFourierMotzkin(Shell::Options::UnificationWithAbstraction::ALASCA_MAIN))  )
      .indices(idxFourierMotzkin())
      .inputs         ({ clause({ -f(fn(au)) > 0, }) 
                       , clause({  f(fn(bu)) > 0  }) })
      .expected(exactly( /* nothing */ ))
    )

TEST_GENERATION(uwa12,
    Generation::SymmetricTest()
      .rule(    move_to_heap(testFourierMotzkin(Shell::Options::UnificationWithAbstraction::ALASCA_MAIN))  )
      .indices(idxFourierMotzkin())
      .inputs         ({ clause({ ab(ff(skx(x0)) + gg(skx(x0))) + -2 * c >= 0 })
                       , clause({-ab(gg(x0)) + c > 0 })
                      })
      .expected(exactly( /* nothing */ ))
    )

TEST_GENERATION(uwa13,
    Generation::SymmetricTest()
      .rule(    move_to_heap(testFourierMotzkin(Shell::Options::UnificationWithAbstraction::ALASCA_MAIN))  )
      .indices(idxFourierMotzkin())
      .inputs         ({ clause({ -2 * c + ab(ff(skx(x0)) + gg(skx(x0))) >= 0 })
                       , clause({-ab(gg(x0)) + c > 0 }) })
      .expected(exactly( /* nothing */ ))
    )


TEST_GENERATION(uwa14,
    Generation::SymmetricTest()
      .rule(    move_to_heap(testFourierMotzkin(Shell::Options::UnificationWithAbstraction::ALASCA_MAIN))  )
      .indices(idxFourierMotzkin())
      .inputs         ({ clause({ -f(2 * x) > 0, }) 
                       , clause({  f(2 * f(y)) > 0  }) })
      .expected(exactly( clause({ BOT }) ))
    )

TEST_GENERATION(uwa14_one_interp,
    Generation::SymmetricTest()
      .rule(    move_to_heap(testFourierMotzkin(Shell::Options::UnificationWithAbstraction::ALASCA_ONE_INTERP))  )
      .indices(idxFourierMotzkin())
      .inputs         ({ clause({ -f(2 * x) > 0, }) 
                       , clause({  f(2 * f(y)) > 0  }) })
      .expected(exactly( clause({ BOT 2 * x != 2 * f(y) }) ))
    )



TEST_GENERATION(greater_equal01a,
    Generation::SymmetricTest()
      .indices(idxFourierMotzkin())
      .inputs  ({ clause({ selected( a + -f(y) >= 0) }) 
               ,  clause({ selected( a +  f(a) >= 0), x - 7 == 0}) })
      .expected(exactly(
            clause({  a + a > 0, -f(a) + a == 0, x - 7 == 0  })
      ))
    )

TEST_GENERATION(greater_equal01b,
    Generation::SymmetricTest()
      .indices(idxFourierMotzkin())
      .inputs  ({ clause({ selected( a + -f(y) >= 0) }) 
               ,  clause({ selected( a +  f(a) >  0), x - 7 == 0}) })
      .expected(exactly(
            clause({  a + a > 0, x - 7 == 0  })
      ))
    )

TEST_GENERATION(greater_equal01c,
    Generation::SymmetricTest()
      .indices(idxFourierMotzkin())
      .inputs  ({ clause({ selected( a + -f(y) >  0) }) 
               ,  clause({ selected( a +  f(a) >= 0), x - 7 == 0}) })
      .expected(exactly(
            clause({  a + a > 0, x - 7 == 0  })
      ))
    )


// ordering condition not fulfilled
// • ( -k s₂ + t₂ >₂ 0 )σ /⪯  ( +j s₁ + t₁ >₁ 0 )σ
TEST_GENERATION(strictly_max_after_unification_0a,
    Generation::SymmetricTest()
      .selfApplications(false)
      .indices(idxFourierMotzkin())
      .inputs  ({ clause({ selected(-f(x) + f(a) > 0) }) 
               ,  clause({ selected( f(a)        > 0) }) })
      .expected(exactly(
          /* nothing */
      ))
    )


TEST_GENERATION(strictly_max_after_unification_01a,
    Generation::SymmetricTest()
      .selfApplications(false)
      .indices(idxFourierMotzkin())
      .inputs  ({ clause({ selected(-2 * f(x) + f(a) > 0) }) 
               ,  clause({ selected( f(a)        > 0) }) })
      .expected(exactly( /* nothing */ ))
    )

TEST_GENERATION(strictly_max_after_unification_01b,
    Generation::SymmetricTest()
      .selfApplications(false)
      .indices(idxFourierMotzkin())
      .inputs  ({ clause({ selected( f(x) - f(a) > 0) }) 
               ,  clause({ selected(-f(a)        > 0) }) })
      .expected(exactly( /* nothing */ ))
    )


TEST_GENERATION(strictly_max_after_unification_02a,
    Generation::SymmetricTest()
      .selfApplications(false)
      .indices(idxFourierMotzkin())
      .inputs  ({        clause({ selected(-f(x) + f(a) > 0 )}) 
               ,         clause({ selected( f(b)        > 0) }) })
      .expected(exactly( clause({           f(a)        > 0 }) ))
    )

TEST_GENERATION(strictly_max_after_unification_02b,
    Generation::SymmetricTest()
      .selfApplications(false)
      .indices(idxFourierMotzkin())
      .inputs  ({        clause({ selected( f(b)        > 0) })  
               ,         clause({ selected(-f(x) + f(a) > 0 )}) })
      .expected(exactly( clause({           f(a)        > 0 }) ))
    )


TEST_GENERATION(max_compared_to_uniterpreted_equalites_01,
    Generation::SymmetricTest()
      .indices(idxFourierMotzkin())
      .inputs  ({        clause({ selected( a > 0), selected( fu(a) == au  ) })  
               ,         clause({ selected(-a > 0 )}) })
      .expected(exactly( /* nothing */ ))
    )

TEST_GENERATION(max_compared_to_uniterpreted_equalites_02,
    Generation::SymmetricTest()
      .indices(idxFourierMotzkin())
      .inputs  ({        clause({ selected( a > 0), selected( fu(a) != au  ) })  
               ,         clause({ selected(-a > 0 )}) })
      .expected(exactly( /* nothing */ ))
    )

TEST_GENERATION(max_compared_to_uniterpreted_equalites_03,
    Generation::SymmetricTest()
      .indices(idxFourierMotzkin())
      .inputs  ({        clause({ selected( fn(fu(a)) > 0), selected( fu(a) == au  ) })  
               ,         clause({ selected(-fn(fu(a)) > 0 )}) })
      .expected(exactly( clause({              BOT            fu(a) == au    })  ))
    )

TEST_GENERATION(max_compared_to_uniterpreted_equalites_04,
    Generation::SymmetricTest()
      .indices(idxFourierMotzkin())
      .inputs  ({        clause({ selected( fn(fu(a)) > 0), selected( fu(a) != au  ) })  
               ,         clause({ selected(-fn(fu(a)) > 0 )}) })
      .expected(exactly( clause({              BOT            fu(a) != au    })  ))
    )

/////////////////////////////////////////////////////////
// Testing substitution application
//////////////////////////////////////

TEST_GENERATION(substitution01,
    Generation::SymmetricTest()
      .indices(idxFourierMotzkin())
      .inputs  ({ clause({ selected(-f(f(x)) + f(x) > 0) })  
               ,  clause({ selected( f(f(a))        > 0) }) })
      .expected(exactly(
            clause({  f(a) > 0 })
      ))
    )

TEST_GENERATION(substitution02,
    Generation::SymmetricTest()
      .indices(idxFourierMotzkin())
      .inputs  ({ clause({ selected( g(f(x), f(f(b))) +    f(x)  > 0) })  
               ,  clause({ selected(-g(f(a), f(f(y))) +    f(y)  > 0) }) })
      .expected(exactly(
            clause({  f(a) + f(b) > 0 })
      ))
    )

/////////////////////////////////////////////////////////
// Testing abstraction
//////////////////////////////////////

TEST_GENERATION(abstraction1,
    Generation::SymmetricTest()
      .indices(idxFourierMotzkin())
      .inputs  ({ clause({ selected(-f(   f(y)       ) > 0) })  
               ,  clause({ selected( f(f(a) + g(b, c)) > 0) }) })
      .expected(exactly(

      ))
    )

TEST_GENERATION(abstraction1_one_interp,
    Generation::SymmetricTest()
      .rule(move_to_heap(testFourierMotzkin(Shell::Options::UnificationWithAbstraction::ALASCA_ONE_INTERP)))
      .indices(idxFourierMotzkin())
      .inputs  ({ clause({ selected(-f(   f(y)       ) > 0) })  
               ,  clause({ selected( f(f(a) + g(b, c)) > 0) }) })
      .expected(exactly(
            clause({ BOT f(a) + g(b, c) != f(y) })
      ))
    )

TEST_GENERATION(abstraction2,
    Generation::SymmetricTest()
      .rule(    move_to_heap(testFourierMotzkin(Options::UnificationWithAbstraction::ALASCA_MAIN))  )
      .indices(idxFourierMotzkin())
      .inputs  ({         clause({ selected(-f(   f(y)       ) > 0) })  
               ,          clause({ selected( f(f(a) + g(b, c)) > 0) }) })
      .expected(exactly(                                                  ))
    )

TEST_GENERATION(abstraction2_one_interp,
    Generation::SymmetricTest()
      .rule(    move_to_heap(testFourierMotzkin(Options::UnificationWithAbstraction::ALASCA_ONE_INTERP))  )
      .indices(idxFourierMotzkin())
      .inputs  ({         clause({ selected(-f(   f(y)       ) > 0) })  
               ,          clause({ selected( f(f(a) + g(b, c)) > 0) }) })
      .expected(exactly(  clause({ BOT f(a) + g(b, c) != f(y)  }) ))
    )

TEST_GENERATION(abstraction3,
    Generation::SymmetricTest()
      .rule(    move_to_heap(testFourierMotzkin(Options::UnificationWithAbstraction::ALASCA_MAIN))  )
      .indices(idxFourierMotzkin())
      .inputs  ({ clause({ selected(-f(b) > 0) })  
               ,  clause({ selected( f(a) > 0) }) })
      .expected(exactly())
    )

TEST_GENERATION(abstraction5,
    Generation::SymmetricTest()
      .rule(    move_to_heap(testFourierMotzkin(Options::UnificationWithAbstraction::ALASCA_MAIN))  )
      .indices(idxFourierMotzkin())
      .inputs  ({        clause({ selected(-f(a + b) > 0) })  
               ,         clause({ selected( f(7 * a) > 0) }) })
      .expected(exactly(                                        ))
    )

TEST_GENERATION(abstraction5_one_interp,
    Generation::SymmetricTest()
      .rule(    move_to_heap(testFourierMotzkin(Options::UnificationWithAbstraction::ALASCA_ONE_INTERP))  )
      .indices(idxFourierMotzkin())
      .inputs  ({        clause({ selected(-f(a + b) > 0) })  
               ,         clause({ selected( f(7 * a) > 0) }) })
      .expected(exactly( clause({ BOT a + b != 7 * a }) ))
    )

TEST_GENERATION(abstraction6,
    Generation::SymmetricTest()
      .rule(    move_to_heap(testFourierMotzkin(Options::UnificationWithAbstraction::ALASCA_MAIN))  )
      .indices(idxFourierMotzkin())
      .inputs  ({        clause({ selected(-f(g(a,x)) > 0) })  
               ,         clause({ selected( f(7 * y)  > 0) }) })
      .expected(exactly( clause({ BOT                  }) ))
    )

TEST_GENERATION(abstraction6_one_interp,
    Generation::SymmetricTest()
      .rule(    move_to_heap(testFourierMotzkin(Options::UnificationWithAbstraction::ALASCA_ONE_INTERP))  )
      .indices(idxFourierMotzkin())
      .inputs  ({        clause({ selected(-f(g(a,x)) > 0) })  
               ,         clause({ selected( f(7 * y)  > 0) }) })
      .expected(exactly( clause({ BOT g(a,x) != 7 * y }) ))
    )

TEST_GENERATION(abstraction7,
    Generation::SymmetricTest()
      .rule(    move_to_heap(testFourierMotzkin(Options::UnificationWithAbstraction::ALASCA_MAIN))  )
      .indices(idxFourierMotzkin())
      .inputs  ({        clause({ selected(-f(a + b) > 0) })
               ,         clause({ selected(     f(c) > 0) })              })
      .expected(exactly(                                     ))
    )

TEST_GENERATION(abstraction7_one_interp,
    Generation::SymmetricTest()
      .rule(    move_to_heap(testFourierMotzkin(Options::UnificationWithAbstraction::ALASCA_ONE_INTERP))  )
      .indices(idxFourierMotzkin())
      .inputs  ({        clause({ selected(-f(a + b) > 0) })
               ,         clause({ selected(     f(c) > 0) })              })
      .expected(exactly( clause({ BOT a + b != c })  ))
    )

TEST_GENERATION(abstraction8,
    Generation::SymmetricTest()
      .rule(    move_to_heap(testFourierMotzkin(Options::UnificationWithAbstraction::ALASCA_MAIN))  )
      .indices(idxFourierMotzkin())
      .inputs  ({        clause({ selected(-f(c + b) > 0) })
               ,         clause({ selected(     f(a) > 0) })              })
      .expected(exactly(                                    ))
    )

TEST_GENERATION(abstraction8_one_interp,
    Generation::SymmetricTest()
      .rule(    move_to_heap(testFourierMotzkin(Options::UnificationWithAbstraction::ALASCA_ONE_INTERP))  )
      .indices(idxFourierMotzkin())
      .inputs  ({        clause({ selected(-f(c + b) > 0) })
               ,         clause({ selected(     f(a) > 0) })              })
      .expected(exactly( clause({ BOT a != c + b }) ))
    )

TEST_GENERATION(abstraction1_alasca2,
    Generation::SymmetricTest()
      .rule(    move_to_heap(testFourierMotzkin(Options::UnificationWithAbstraction::ALASCA_MAIN))  )
      .indices(idxFourierMotzkin())
      .inputs  ({        clause({ -f(a + b) > 0 })
               ,         clause({  f(c) > 0 })              })
      .expected(exactly( /* nothing */                      ))
    )

TEST_GENERATION(abstraction2_alasca2,
    Generation::SymmetricTest()
      .rule(    move_to_heap(testFourierMotzkin(Options::UnificationWithAbstraction::ALASCA_MAIN))  )
      .indices(idxFourierMotzkin())
      .inputs  ({        clause({ selected(-f(a + b) > 0) })
               ,         clause({ selected( f(c + x) > 0) })              })
      .expected(exactly( clause({  BOT                   }) ))
    )

TEST_GENERATION(abstraction2_alasca2_one_interp,
    Generation::SymmetricTest()
      .rule(    move_to_heap(testFourierMotzkin(Options::UnificationWithAbstraction::ALASCA_ONE_INTERP))  )
      .indices(idxFourierMotzkin())
      .inputs  ({        clause({ selected(-f(a + b) > 0) })
               ,         clause({ selected( f(c + x) > 0) })              })
      .expected(exactly( clause({  BOT c + x != a + b   }) ))
    )

TEST_GENERATION(abstraction3_alasca2,
    Generation::SymmetricTest()
      .rule(    move_to_heap(testFourierMotzkin(Options::UnificationWithAbstraction::ALASCA_MAIN))  )
      .indices(idxFourierMotzkin())
      .inputs  ({        clause({ -f(3 * a) > 0 })
               ,         clause({  f(4 * a) > 0 })              })
      .expected(exactly(   ))
    )

TEST_GENERATION(abstraction4,
    Generation::SymmetricTest()
      .rule(    move_to_heap(testFourierMotzkin(Options::UnificationWithAbstraction::ALASCA_MAIN))  )
      .indices(idxFourierMotzkin())
      .inputs  ({        clause({ -f(3 * a) > 0 })  
               ,         clause({  f(7 * a) > 0 }) })
      .expected(exactly(                                            ))
    )

TEST_GENERATION(abstraction4_one_interp,
    Generation::SymmetricTest()
      .rule(    move_to_heap(testFourierMotzkin(Options::UnificationWithAbstraction::ALASCA_ONE_INTERP))  )
      .indices(idxFourierMotzkin())
      .inputs  ({        clause({ -f(3 * a) > 0 })  
               ,         clause({  f(7 * a) > 0 }) })
      .expected(exactly( clause({    BOT 3 * a != 7 * a  }) ))
    )


TEST_GENERATION(abstraction9,
    Generation::SymmetricTest()
      .rule(    move_to_heap(testFourierMotzkin(Options::UnificationWithAbstraction::ALASCA_MAIN))  )
        .indices(idxFourierMotzkin())
        .inputs  ({        clause({ -f( a ) > 0 })
                 ,         clause({  f( a + f(b) ) > 0 })        })
        .expected(exactly( /* nothing */                         ))
      )

TEST_GENERATION(abstraction9_one_interp,
    Generation::SymmetricTest()
      .rule(    move_to_heap(testFourierMotzkin(Options::UnificationWithAbstraction::ALASCA_ONE_INTERP))  )
        .indices(idxFourierMotzkin())
        .inputs  ({        clause({ -f( a ) > 0 })
                 ,         clause({  f( a + f(b) ) > 0 })        })
        .expected(exactly( clause({ BOT a != a + f(b) }) ))
      )


  /////////////////////////////////////////////////////////
  // Testing normalization
  //////////////////////////////////////

  TEST_GENERATION(misc01,
      Generation::SymmetricTest()
        .indices(idxFourierMotzkin())
        .inputs  ({ clause({ selected(a + -f(a) > 0    ) }) 
                 ,  clause({ selected(f(a) > 0) }) })
        .expected(exactly(
              clause({  a > 0  })
        ))
      )

  TEST_GENERATION_WITH_SUGAR(misc02_INT,
      SUGAR(Int),
      Generation::SymmetricTest()
        .indices(idxFourierMotzkin())
        .inputs  ({ clause({selected(a + -f(a) + 1 > 0 )  }) 
                 ,  clause({selected(f(a) > 0) }) }) 
        .expected(exactly(
              clause({ -1 + a + 1 > 0  })
        ))
      )

  TEST_GENERATION_WITH_SUGAR(misc02_Rat,
      SUGAR(Rat),
      Generation::SymmetricTest()
        .indices(idxFourierMotzkin())
        .inputs  ({ clause({selected( a + -f(a) >= 0)  }) 
                 ,  clause({selected(f(a) > 0) }) })
        .expected(exactly(
              clause({  a > 0  })
        ))
      )

  // only for integers (which we r using here)
  TEST_GENERATION_WITH_SUGAR(misc03,
      SUGAR(Int),
      Generation::SymmetricTest()
        .indices(idxFourierMotzkin())
        .inputs  ({ clause({selected( f(a) + 1 > 0) }) 
                 ,  clause({selected(a + -f(a) > 0) }) })
        .expected(exactly(
              clause({ -1 +  a + 1 > 0  })
        ))
      )

  TEST_GENERATION_WITH_SUGAR(bug01a,
      SUGAR(Real),
      Generation::SymmetricTest()
      .indices(idxFourierMotzkin())
      .inputs  ({ clause({ selected(r(x, y)),  (f(x) + -f(y) > 0)  }) 
               ,  clause({ selected(f(a) >  0) }) })
      //                                      (y - 1 > 0) 
      .expected(exactly(
      ))
    )

TEST_GENERATION_WITH_SUGAR(misc02a,
    SUGAR(Real),
    Generation::SymmetricTest()
      .indices(idxFourierMotzkin())
      .inputs  ({        clause({ selected( -3 +  a  > 0 ) })  
               ,         clause({ selected(  0 + -a  > 0 ) }) })
      .expected(exactly( clause({            num(-3) > 0   }) ))
    )

TEST_GENERATION_WITH_SUGAR(misc02b,
    SUGAR(Real),
    Generation::SymmetricTest()
      .indices(idxFourierMotzkin())
      .inputs  ({        clause({ selected(  0 +  a  > 0 ) })  
               ,         clause({ selected( -3 + -a  > 0 ) }) })
      .expected(exactly( clause({            num(-3) > 0   }) ))
    )

TEST_GENERATION_WITH_SUGAR(bug03a,
    SUGAR(Real),
    Generation::SymmetricTest()
// *cl2 = ~P(X1,X2) | 1 + -X1 + a > 0
// *resolvent = $greater($sum(1,$uminus(X1)),0) | ~'MS'(X0,X1,s2)
      .indices(idxFourierMotzkin())
      .inputs  ({        clause({            selected(1 + -f(a)        > 0) })  
               ,         clause({  selected(~r(y,z)), 1 + -f(x) + f(a) > 0  }) })
      .expected(exactly(                      ))
    )

TEST_GENERATION_WITH_SUGAR(bug03b,
    SUGAR(Real),
    Generation::SymmetricTest()
      .selfApplications(false)
// *cl2 = ~P(X1,X2) | 1 + -X1 + a > 0
// *resolvent = $greater($sum(1,$uminus(X1)),0) | ~'MS'(X0,X1,s2)
      .indices(idxFourierMotzkin())
      .inputs  ({        clause({               selected(1 + -f(a)            > 0) })  
               ,         clause({  a - 1 != 0 , selected(1 + -f(x) + f(a)     > 0) }) })
      .expected(exactly( clause({  a - 1 != 0 ,          1 + -f(x)        + 1 > 0  }) ))
    )


TEST_GENERATION_WITH_SUGAR(bug_uwa_01,
    SUGAR(Real),
    Generation::SymmetricTest()
      .selfApplications(false)
      .rule(    move_to_heap(testFourierMotzkin(Options::UnificationWithAbstraction::ALASCA_MAIN))  )
      .indices(idxFourierMotzkin())
  // (not (P (+ x1 x0) (+ x2 x0))) (P x1 x2))))
  //      (P x0 x0)
  // ; ==================================
  // (P x0 x1)
      .inputs  ({ clause({ -g(x1 + x0, x2 + x0) + g(x1, x2) > 0 })  
               ,  clause({  g(x0, x0) > 0 }) })
      .expected(exactly(
          clause({  g(x0, x0) > 0  })
          // clause({ BOT }) // we don't perform the rule if we overflow
      ))
    )

#define LIMIT_SUGAR                                                                       \
  NUMBER_SUGAR(Real)                                                                      \
  DECL_DEFAULT_VARS                                                                       \
  DECL_FUNC(ab, {Real}, Real)                                                             \
  DECL_FUNC(skx, {Real}, Real)                                                            \
  DECL_FUNC(gg, {Real}, Real)                                                             \
  DECL_CONST(delta, Real)                                                                 \
  DECL_CONST(a, Real)                                                                     \


TEST_GENERATION_WITH_SUGAR(bug_uwa_02,
    SUGAR(Real),
    Generation::SymmetricTest()
      .selfApplications(false)
      .rule(    move_to_heap(testFourierMotzkin(Options::UnificationWithAbstraction::ALASCA_MAIN))  )
      .indices(idxFourierMotzkin())
// 19. (-delta + ab((a + skx(X0)))) > 0/1 [theory normalization 13]
// 23. (c + -ab(gg(X0))) > 0/1 | (delta + -ab((X0 + a))) >= 0/1 [theory normalization 17]
      .inputs  ({ clause({ -delta + ab(a + skx(x)) > 0 })
                , clause({ delta + -ab(x + a) >= 0 })
               })
      .expected(exactly(
          clause({ -delta + delta > 0 })
          // clause({ BOT }) // we don't perform the rule if we overflow
      ))
    )

TEST_GENERATION_WITH_SUGAR(bug_uwa_03,
    SUGAR(Real),
    Generation::SymmetricTest()
      .selfApplications(false)
      .rule(    move_to_heap(testFourierMotzkin(Options::UnificationWithAbstraction::ALASCA_MAIN))  )
      .indices(idxFourierMotzkin())
// 19. (-delta + ab((a + skx(X0)))) > 0/1 [theory normalization 13]
// 23. (c + -ab(gg(X0))) > 0/1 | (delta + -ab((X0 + a))) >= 0/1 [theory normalization 17]
      .inputs  ({ clause({ -delta + ab(a + skx(x)) > 0 })
                , clause({ c + -ab(gg(x)) > 0 })
               })
      .expected(exactly(
          // clause({ -delta + delta > 0, x + a != skx(x) + a, c + -ab(gg(x)) > 0 })
          // clause({ BOT }) // we don't perform the rule if we overflow
      ))
    )

TEST_GENERATION_WITH_SUGAR(bug_uwa_04,
    SUGAR(Real),
    Generation::SymmetricTest()
      .selfApplications(false)
      .rule(    move_to_heap(testFourierMotzkin(Options::UnificationWithAbstraction::ALASCA_MAIN))  )
      .indices(idxFourierMotzkin())
// 19. (-delta + ab((a + skx(X0)))) > 0/1 [theory normalization 13]
// 23. (c + -ab(gg(X0))) > 0/1 | (delta + -ab((X0 + a))) >= 0/1 [theory normalization 17]
      .inputs  ({ clause({ -delta + ab(a + skx(x)) > 0 })
                , clause({ c + -ab(gg(x)) > 0, delta + -ab(x + a) >= 0 })
               })
      .expected(exactly(
      ))
    )



TEST_GENERATION_WITH_SUGAR(bug_overflow_01,
    SUGAR(Real),
    Generation::SymmetricTest()
      .indices(idxFourierMotzkin())
      .inputs  ({ clause({ selected(          num(2) * (1073741824 * a + 536870912) > 0 ) })  
               ,  clause({ selected(num(-1) * num(2) * (1073741824 * a + 536870912) > 0 )   }) })
      .expected(exactly(
          clause({  2 * -num(1) + 2 > 0  })
          // clause({ BOT }) // we don't perform the rule if we overflow
      ))
    )

  // 2 f13(f14, 1) 1073741824

TEST_GENERATION_WITH_SUGAR(bug_overflow_02,
    SUGAR(Int),
    Generation::SymmetricTest()
      .indices(idxFourierMotzkin())
      .inputs  ({ clause({ selected( 0 < 2 * (f(a) * num(1073741824)) ) })  
               ,  clause({ selected( 3  + -a > 0 )  }) })
      .expected(exactly(
      ))
    )


TEST_GENERATION_WITH_SUGAR(misc04_one_interp,
    SUGAR(Real),
    Generation::SymmetricTest()
      .rule(move_to_heap(testFourierMotzkin(Shell::Options::UnificationWithAbstraction::ALASCA_ONE_INTERP)))
      .indices(idxFourierMotzkin())
      .inputs  ({        clause({ selected(-f(x0 + -x1 + g(x0,x1)) > 0) })
               ,         clause({ selected( f(x2 + -g(x3,x2)     ) > 0) }) })
      .expected(exactly( clause({                           BOT x0 + -x1 + g(x0,x1) != x2 + -g(x3,x2) })))
    )


TEST_GENERATION_WITH_SUGAR(bug05_one_interp,
    SUGAR(Real),
    Generation::AsymmetricTest()
      .rule(move_to_heap(testFourierMotzkin(Shell::Options::UnificationWithAbstraction::ALASCA_ONE_INTERP)))
      .indices(idxFourierMotzkin())
      .input   (         clause({ selected(-f(x0 + 3 * a) > 0) }))
      .context ({        clause({ selected( f(x1 + a0   ) > 0) })
                ,        clause({ selected( f(x1 + a1   ) > 0) })
                ,        clause({ selected( f(x2 + a2   ) > 0) }) 
                ,        clause({ selected( f(a  + a3   ) > 0) }) 
                ,        clause({ selected( f(b  + a3   ) > 0) }) 
                })
      .expected(exactly( clause({         BOT x0 + 3 * a != x3 + a0 })
                       , clause({         BOT x0 + 3 * a != x4 + a1 })
                       , clause({         BOT x0 + 3 * a != x5 + a2 })
                       , clause({         BOT x0 + 3 * a != a  + a3 })
                       , clause({         BOT x0 + 3 * a != b  + a3 })
                       ))
    )


TEST_GENERATION_WITH_SUGAR(bug05,
    SUGAR(Real),
    Generation::AsymmetricTest()
      .rule(move_to_heap(testFourierMotzkin(Shell::Options::UnificationWithAbstraction::ALASCA_MAIN)))
      .indices(idxFourierMotzkin())
      .input   (         clause({ selected(-f(x0 + 3 * a) > 0) }))
      .context ({        clause({ selected( f(x1 + a0   ) > 0) })
                ,        clause({ selected( f(x1 + a1   ) > 0) })
                ,        clause({ selected( f(x2 + a2   ) > 0) }) 
                ,        clause({ selected( f(a  + a3   ) > 0) }) 
                ,        clause({ selected( f(b  + a3   ) > 0) }) 
                })
      .expected(exactly( clause({         BOT })
                       , clause({         BOT })
                       , clause({         BOT })
                       , clause({         BOT })
                       , clause({         BOT })
                       ))
    )

TEST_GENERATION_WITH_SUGAR(bug06,
    SUGAR(Real),
    Generation::SymmetricTest()
      .indices(idxFourierMotzkin())
      .inputs  ({ clause({  gg(x) >= 0   , delta + -ab(x + 1) >= 0, c > 0 })
                , clause({ -gg(x) + c > 0, delta + -ab(x + 1) >= 0, -gg(x) > 0 })
                })
      .expected(exactly(  clause({ delta + -ab(x + 1) >= 0, c > 0
                                 , delta + -ab(x + 1) >= 0, -gg(x) > 0,
                                 c > 0
                                 })
                       ))
    )

#define _SUM(L,R) (L + R)

TEST_GENERATION_WITH_SUGAR(bug07,
    SUGAR(Real),
    Generation::AsymmetricTest()
      .indices(idxFourierMotzkin())
      .input  ( clause({ -gg(x) + c > 0, delta + -ab(x + 1) >= 0, -gg(x) > 0 }) )
      .context({
                clause({ _SUM(ab(1 + skx(x)),-delta) > 0 , }) // 19
              , clause({ 0 == _SUM(-x,-ab(x)) , x >= 0 , }) // 21
              , clause({ 0 == _SUM(-x,ab(x)) , -x > 0 , }) // 22
              , clause({ -z > 0 , z >= 0 , 0 == -z , }) // 29
              , clause({ _SUM(ab(ff(skx(x)) + gg(skx(x))),(-2 * c)) >= 0 , }) // 20
              , clause({ _SUM(delta,-ab(x + 1)) >= 0 , _SUM(c,-ab(gg(x))) > 0 , }) // 23
              , clause({ 0 != _SUM(x,-skx(x3)) , _SUM(c,-ab(gg(x))) > 0 , }) // 50
              , clause({ _SUM(-1,_SUM(-skx(x),-delta)) > 0 , _SUM(1,skx(x)) >= 0 , }) // 26
              , clause({ _SUM(1,_SUM(skx(x),-delta)) > 0 , _SUM(-1,-skx(x)) > 0 , }) // 30
              , clause({ _SUM(delta,-ab(x + 1)) >= 0 , _SUM(c,-ab(ff(x))) > 0 , }) // 24
              , clause({ 0 != _SUM(x,-skx(x3)) , _SUM(c,-ab(ff(x))) > 0 , }) // 77
              , clause({ 0 != _SUM(z,-skx(x3)) , gg(z) >= 0 , _SUM(c,gg(z)) > 0 , }) // 56
              , clause({ 0 != _SUM(x,-skx(y)) , gg(x) >= 0 , c > 0 , }) // 86
              , clause({ _SUM(delta,-ab(1 + y)) >= 0 , gg(y) >= 0 , _SUM(c,gg(y)) > 0 , }) // 43
              , clause({ _SUM(delta,-ab(x + 1)) >= 0 , gg(x) >= 0 , c > 0 , }) // 102
              , clause({ _SUM(-1,-skx(x)) > 0 , _SUM(1,skx(x)) >= 0 , -delta > 0 , }) // 61
              , clause({ 0 != _SUM(z,-skx(x3)) , ff(z) >= 0 , _SUM(c,ff(z)) > 0 , }) // 83
              , clause({ _SUM(delta,-ab(1 + y)) >= 0 , ff(y) >= 0 , _SUM(c,ff(y)) > 0 , }) // 70
              , clause({ 0 != _SUM(x,-skx(y)) , ff(x) >= 0 , c > 0 , }) // 112
              , clause({ _SUM(delta,-ab(x + 1)) >= 0 , ff(x) >= 0 , c > 0 , }) // 127
              , clause({ 0 != _SUM(x,-skx(y)) , _SUM(c,gg(x)) > 0 , -c >= 0 , }) // 87
              , clause({ _SUM(c,-ab(gg(y))) > 0 , _SUM(1,y) >= 0 , _SUM(1,_SUM(delta,y)) >= 0 , }) // 44
              , clause({ 0 != _SUM(x,-skx(y)) , _SUM(c,ff(x)) > 0 , -c >= 0 , }) // 113
              , clause({ 0 != _SUM(x,-skx(y)) , -gg(x) > 0 , _SUM(c,-gg(x)) > 0 , }) // 53
              , clause({ 0 != _SUM(x,-skx(y)) , c > 0 , -gg(x) > 0 , }) // 157
              , clause({ _SUM(c,-ab(ff(y))) > 0 , _SUM(1,y) >= 0 , _SUM(1,_SUM(delta,y)) >= 0 , }) // 71
              , clause({ 0 != _SUM(x,-skx(y)) , c > 0 , }) // 173
              , clause({ c > 0 , }) // 189
              , clause({ 0 != _SUM(x,-skx(y)) , -ff(x) > 0 , _SUM(c,-ff(x)) > 0 , }) // 80
              , clause({ _SUM(delta,-ab(x + 1)) >= 0 , -gg(x) > 0 , _SUM(c,-gg(x)) > 0 , }) // 41

        })
      .expected(
            contains(
                        clause({ delta + -ab(x + 1) >= 0, c > 0
                                 , delta + -ab(x + 1) >= 0, -gg(x) > 0,
                                 c > 0
                                 })
              )
    )
      )


// [       is ]: [ $greater(0.0, 0.0) | ~((((15.0 * X0) + ((-15.0 * X1) + g((15.0 * X0), X1))) = ((15.0 * X2) + $uminus(g(X3, X2))))) ]
// [ expected ]: [ $greater(0.0, 0.0) | ~(((((15.0 * X0) + (-15.0 * X1)) + g((15.0 * X0), X1)) = ((15.0 * X0) + $uminus(g(X2, X0))))) ]


// TEST_GENERATION_WITH_SUGAR(uwa_floor_1,
//     SUGAR(Real),
//     Generation::SymmetricTest()
//     .
//       .indices(idxFourierMotzkin())
//       .inputs  ({ clause({ selected( f(num(123)) > 0 ) })  
//                ,  clause({ selected( -f(floor(x)) + a > 0 )  }) })
//       .expected(exactly(
//           clause({ a > 0 })
//       ))
//     )

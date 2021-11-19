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

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// TEST CASES 
/////////////////////////////////////

#define SUGAR(Num)                                                                                            \
  NUMBER_SUGAR(Num)                                                                                           \
  DECL_DEFAULT_VARS                                                                                           \
  DECL_FUNC(f, {Num}, Num)                                                                                    \
  DECL_FUNC(g, {Num}, Num)                                                                                    \
  DECL_FUNC(g2, {Num, Num}, Num)                                                                              \
  DECL_CONST(a, Num)                                                                                          \
  DECL_CONST(b, Num)                                                                                          \
  DECL_CONST(c, Num)                                                                                          \
  DECL_PRED(p, {Num})                                                                                         \
  DECL_PRED(r, {Num,Num})                                                                                     \
  \
  DECL_SORT(alpha) \
  DECL_FUNC(fa, {Num}, alpha) \
  DECL_CONST(aa, alpha) \
  DECL_CONST(ba, alpha) \

#define MY_SYNTAX_SUGAR SUGAR(Rat)

#define UWA_MODE Options::UnificationWithAbstraction::IRC1

Indexing::Index* ircSuperpositionIndex() 
{ return new Indexing::IRCSuperpositionIndex(new TermSubstitutionTree(UWA_MODE, true)); }

Superposition testSuperposition()
{ return Superposition(testIrcState(UWA_MODE)); }



REGISTER_GEN_TESTER(Test::Generation::GenerationTester<Superposition>(testSuperposition()))

/////////////////////////////////////////////////////////
// Basic tests
//////////////////////////////////////

TEST_GENERATION(basic01,
    Generation::TestCase()
      .indices({ ircSuperpositionIndex() })
      .input   (  clause({ selected( 3 * f(x) - 4 == 0 )  }) )
      .context ({ clause({ selected(     3 * f(x) >  0 )  }) })
      .expected(exactly(
            clause({ 3 * frac(4,3) > 0  })
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION(basic02,
    Generation::TestCase()
      .indices({ ircSuperpositionIndex() })
      .input   (  clause({ selected( 3 * f(x) - 4 == 0 )  }) )
      .context ({ clause({ selected(     f(x) >  0 )  }) })
      .expected(exactly(
            clause({ frac(4, 3) > 0  })
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION(basic03,
    Generation::TestCase()
      .indices({ ircSuperpositionIndex() })
      .input   (  clause({selected( f(a) + a + 3 == 0 ) })  )
      .context ({ clause({selected( f(x) > 0 ) }) })
      .expected(exactly(
            clause({ - a + -3 > 0  })
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION(basic04,
    Generation::TestCase()
      .indices({ ircSuperpositionIndex() })
      .input   (  clause({ selected( f(a) + a + 3 == 0 ) })  )
      .context ({ clause({  f(x) > 0, selected(f(g(x)) > 0) }) })
      .expected(exactly(
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION(basic05,
    Generation::TestCase()
      .indices({ ircSuperpositionIndex() })
      .input   (  clause({selected( f(a) + a + 3 == 0 ) })  )
      .context ({ clause({selected( p(f(x)) ) }) })
      .expected(exactly(
            clause({ p(- a + -3)  })
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION(basic06,
    Generation::TestCase()
      .indices({ ircSuperpositionIndex() })
      .input   (  clause({selected( f(a) + a + 3 == 0 ) })  )
      .context ({ clause({selected( g(f(x)) != 0 ) }) })
      .expected(exactly(
            clause({ g(-a + -3) != 0 })
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION(basic07,
    Generation::TestCase()
      .indices({ ircSuperpositionIndex() })
      .input   (  clause({selected( f(a) + a + 3 == 0 ) })  )
      .context ({ clause({selected( g(3 * f(x)) != 0 ) }) })
      .expected(exactly(
            clause({ g(3 * (-a + -3)) != 0 })
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION(uwa1,
    Generation::TestCase()
      .indices({ ircSuperpositionIndex() })
      .input   (  clause({ selected( f(a + x) - 4 == 0 )  }) )
      .context ({ clause({ selected( f(b) >  0 )  }) })
      .expected(exactly(
            clause({ num(4) > 0, a + x != b  })
      ))
      .premiseRedundant(false)
    )


TEST_GENERATION(misc01,
    Generation::TestCase()
      .indices({ ircSuperpositionIndex() })
      .input   (          clause({ 0 == -17 + a }) ) // ==> a == 17
      .context ({         clause({ -19 + -f(x) + a * y  >= 0 }) })
      .expected(exactly(  clause({ -19 + -f(x) + 17 * y >= 0 }) ))
      .premiseRedundant(false)
    )

// • ( u[s2] + t2 ≈ 0)σ is strictly maximal in Hyp2σ
TEST_GENERATION(ordering1_ok,
    Generation::TestCase()
      .indices({ ircSuperpositionIndex() })
      .input   (          clause({ g2(a,a) == 0 }) )
      .context ({         clause({ f(g2(x,y)) > 0, f(g2(z,z)) > 0 }) }) 
      .expected(exactly(  clause({ f(0) > 0, f(g2(x,x)) > 0 }) 
                       ,  clause({ f(0) > 0, f(g2(y,z)) > 0 }) ))
      .premiseRedundant(false)
    )
TEST_GENERATION(ordering1_fail,
    Generation::TestCase()
      .indices({ ircSuperpositionIndex() })
      .input   (          clause({ g2(a,a) == 0 }) )
      .context ({         clause({ f(g2(x,y)) > 0, f(g2(y,x)) > 0 }) }) 
      .expected(exactly(  /* nothing */          ))
      .premiseRedundant(false)
    )

// • (±k. s1 + t1 ≈ 0)σ is strictly maximal in Hyp1σ
TEST_GENERATION(ordering2_ok,
    Generation::TestCase()
      .indices({ ircSuperpositionIndex() })
      .input   (          clause({ g2(x,y) == 0, g2(z,z) == 0 }) )
      .context ({         clause({ f(g2(a,a)) > 0 }) }) 
      .expected(exactly(  clause({ f(0) > 0, g2(x,x) == 0 }) 
                       ,  clause({ f(0) > 0, g2(x,y) == 0 }) ))
      .premiseRedundant(false)
    )
TEST_GENERATION(ordering2_fail,
    Generation::TestCase()
      .indices({ ircSuperpositionIndex() })
      .input   (          clause({ g2(x,y) == 0, g2(y,x) == 0 }) )
      .context ({         clause({ f(g2(a,a)) > 0 }) }) 
      .expected(exactly(  /* nothing */  ))
      .premiseRedundant(false)
    )

// •        s1  σ is strictly maximal in terms(s1 + t1)σ
TEST_GENERATION(ordering3_ok,
    Generation::TestCase()
      .indices({ ircSuperpositionIndex() })
      .input   (          clause({ g2(x,y) + g2(z,z) + g2(z,z) == 0 }) )
      .context ({         clause({ f(g2(a,a)) > 0 }) }) 
      .expected(exactly(  clause({ f(       -2  * g2(z,z)) > 0 }) 
                       ,  clause({ f(frac(-1,2) * g2(x,y)) > 0 }) ))
      .premiseRedundant(false)
    )
TEST_GENERATION(ordering3_fail,
    Generation::TestCase()
      .indices({ ircSuperpositionIndex() })
      .input   (          clause({  g2(x,y) + g2(y,x) + g2(y,x) == 0 }) )
      .context ({         clause({ f(g2(a,a)) > 0 }) }) 
      .expected(exactly(  /* nothing */  ))
      .premiseRedundant(false)
    )


TEST_GENERATION(uninterpreted_pred_1,
    Generation::TestCase()
      .indices({ ircSuperpositionIndex() })
      .input   (         clause({ selected(   f(x) - 1 == 0 )  })  )
      .context ({        clause({ selected( p(f(x)) )          }) })
      .expected(exactly( clause({           p(1)               })
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION(uninterpreted_pred_2,
    Generation::TestCase()
      .indices({ ircSuperpositionIndex() })
      .input   (         clause({ selected(   f(x) - 1 == 0 )      })  )
      .context ({        clause({ selected( p(f(a)) ), f(f(b)) > 0 }) })
      .expected(exactly( clause({           p(1)     , f(f(b)) > 0 }) ))
      .premiseRedundant(false)
    )

TEST_GENERATION(uninterpreted_pred_3, // TODO couldn't we replace all occurences of f(x) instead of the maximal one
    Generation::TestCase()
      .indices({ ircSuperpositionIndex() })
      .input   (         clause({ selected(   f(x) - 1 == 0 )      })  )
      .context ({        clause({ selected( p(f(x)) ), f(f(x)) > 0 }) })
      .expected(exactly( clause({           p(1)     , f(f(x)) > 0 }) ))
      .premiseRedundant(false)
    )

TEST_GENERATION(uninterpreted_sort_1,
    Generation::TestCase()
      .indices({ ircSuperpositionIndex() })
      .input   (         clause({ selected( f(x) - 1 == 0  ) })  )
      .context ({        clause({ selected( fa(f(x)) == aa ) }) })
      .expected(exactly( clause({           fa(  1 ) == aa   }) ))
      .premiseRedundant(false)
    )

TEST_GENERATION(uninterpreted_sort_2,
    Generation::TestCase()
      .indices({ ircSuperpositionIndex() })
      .input   (         clause({ selected( f(x) - 1 == 0  ) })  )
      .context ({        clause({ selected( fa(3 *   f(x)) == aa ) }) })
      .expected(exactly( clause({           fa(3 * num(1)) == aa   }) ))
      .premiseRedundant(false)
    )


  // TODO test if forward and backward r symmetric

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
#include "Inferences/ALASCA/TermFactoring.hpp"
#include "Lib/STL.hpp"

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

#define SUGAR(Num)                                                                                  \
  NUMBER_SUGAR(Num)                                                                                 \
  DECL_DEFAULT_VARS                                                                                 \
  DECL_VAR(x0, 0)                                                                                   \
  DECL_VAR(x1, 1)                                                                                   \
  DECL_VAR(x2, 2)                                                                                   \
  DECL_VAR(x3, 3)                                                                                   \
  DECL_VAR(x4, 4)                                                                                   \
  DECL_FUNC(f, {Num}, Num)                                                                          \
  DECL_FUNC(ff, {Num}, Num)                                                                         \
  DECL_FUNC(g, {Num, Num}, Num)                                                                     \
  DECL_FUNC(g0, {Num, Num}, Num)                                                                    \
  DECL_FUNC(g1, {Num, Num}, Num)                                                                    \
  DECL_FUNC(h, {Num, Num, Num}, Num)                                                                \
  DECL_CONST(a, Num)                                                                                \
  DECL_CONST(b, Num)                                                                                \
  DECL_CONST(c, Num)                                                                                \
  DECL_PRED(p, {Num})                                                                               \
  DECL_PRED(r, {Num,Num})                                                                           \

#define MY_SYNTAX_SUGAR SUGAR(Rat)


TermFactoring testTermFactoring(
    Options::UnificationWithAbstraction uwa = Options::UnificationWithAbstraction::ALASCA_MAIN
    )
{ return TermFactoring(testAlascaState(uwa)); }

REGISTER_GEN_TESTER(AlascaGenerationTester<TermFactoring>())

/////////////////////////////////////////////////////////
// Basic tests
//////////////////////////////////////

TEST_GENERATION(basic01a,
    Generation::SymmetricTest()
      .inputs  ({  clause({selected( g(a, x) + -g(y, b) > 0 ) }) })
      .expected(exactly(
          clause({ 0 * g(a, b) > 0 })
      )))
TEST_GENERATION(basic01b,
    Generation::SymmetricTest()
      .inputs  ({  clause({selected( g(a, x) + g(y, b) > 0 ) }) })
      .expected(exactly(
          clause({ 2 * g(a, b) > 0 })
      )))

// checking different symbols


#define test_basic03(pred, name)                                                                       \
TEST_GENERATION(basic03_ ## name,                                                                     \
    Generation::SymmetricTest()                                                                     \
      .inputs  ({  clause({selected( pred(g(a, x) + g(y, b))  ) }) })                                \
      .expected(exactly(                                                                            \
          clause({ pred(2 * g(a, b)) })                                                             \
      )))                                                                                           \

test_basic03([](auto x){ return x >= 0; }, geq)
test_basic03([](auto x){ return x >  0; }, greater)
test_basic03([](auto x){ return x == 0; }, eq)
test_basic03([](auto x){ return x != 0; }, neq)

TEST_GENERATION(basic02,
    Generation::SymmetricTest()
      .inputs  ({              clause({ - f(x) + f(y) > 0 }) })
      .expected(exactly(       clause({      0 * f(x) > 0 }) )))

TEST_GENERATION(basic03,
    Generation::SymmetricTest()
      .inputs  ({              clause({ - f(x) - f(y) > 0 }) })
      .expected(exactly(       clause({     -2 * f(x) > 0 }) )))

TEST_GENERATION(basic04,
    Generation::SymmetricTest()
      .inputs  ({              clause({   f(x) + f(y) > 0 }) })
      .expected(exactly(       clause({      2 * f(x) > 0 }) )))


TEST_GENERATION(basic05a,
    Generation::SymmetricTest()
      .inputs  ({  clause({selected( 3 * g(a, x) + 2 * g(y, b) > 0 ), p(x) }) })
      .expected(exactly(
          /* nothing because uninterpreted stuff is bigger */
      )))

TEST_GENERATION(basic05b,
    Generation::SymmetricTest()
      .inputs  ({  clause({selected( 3 * g(a, x) + 2 * g(y, b) > 0 ), f(x) - 1 == 0 }) })
      .expected(exactly(
            clause({ 5 * g(a,b) > 0, f(b) - 1 == 0  })
      )))

TEST_GENERATION(basic06,
    Generation::SymmetricTest()
      .inputs  ({  clause({ selected( 1 * f(x) +  -1 * f(a) > 0 )  }) })
      .expected(exactly(
            clause({      0 * f(a) > 0 }) 
      )))

TEST_GENERATION(basic07a,
    Generation::SymmetricTest()
      .inputs  ({              clause({   f(x) + f(y) != 0 }) })
      .expected(exactly(       clause({      2 * f(x) != 0 }) )))

TEST_GENERATION(basic07b,
    Generation::SymmetricTest()
      .inputs  ({              clause({   f(x) + f(y) == 0 }) })
      .expected(exactly(       clause({      2 * f(x) == 0 }) )))


TEST_GENERATION(basic07c,
    Generation::SymmetricTest()
      .inputs  ({              clause({   f(x) + f(y) >= 0 }) })
      .expected(exactly(       clause({      2 * f(x) >= 0 }) )))


// checking (k1 s1 + k2 s2 + t <> 0)σ /≺ Cσ
TEST_GENERATION(lit_max_after_unif_1,
    Generation::SymmetricTest()
      .inputs  ({  clause({ f(x) +  -f(a) > 0, f(f(a)) > 0 }) })
      .expected(exactly(
      )))

// checking (k1 s1 + k2 s2 + t <> 0)σ /≺ Cσ
TEST_GENERATION(lit_max_after_unif_2,
    Generation::SymmetricTest()
      .inputs  ({  clause({ selected( f(x) +  -f(a) > 0 ), selected( f(f(a)) > 0 ), selected( f(z) > 0 ) }) })
      .expected(exactly(
      )))

// checking (k1 s1 + k2 s2 + t <> 0) /≺ Cσ
TEST_GENERATION(lit_max_after_unif_3,
    Generation::SymmetricTest()
      .inputs  ({        clause({ selected( f(x) +  -f(a) > 0 ), f(z) > 0 }) })
      .expected(exactly( clause({ selected(      0 * f(a) > 0 ), f(z) > 0 }) )))

TEST_GENERATION(term_max_after_unif_0,
    Generation::SymmetricTest()
      .inputs  ({        clause({ f(a + b) + -f(a + b + c) > 0 }) })
      .expected(exactly(                               )))


// checking s1σ /≺ terms(s2 + t)σ
// checking s2σ /≺ terms(s1 + t)σ
TEST_GENERATION(term_max_after_unif_1,
    Generation::SymmetricTest()
      .inputs  ({        clause({ g(a + x, c) + -g(a + b + x, x) > 0 }) })
      .expected(exactly(                               )))

// checking s1σ /≺ terms(s2 + t)σ
// checking s2σ /≺ terms(s1 + t)σ
TEST_GENERATION(term_max_after_unif_2,
    Generation::SymmetricTest()
      .inputs  ({        clause({ g(a, c) + -g(a, x) + g(x, x) > 0 }) })
      .expected(exactly(                               )))

TEST_GENERATION(basic07,
    Generation::SymmetricTest()
      .inputs  ({  clause({ selected( 1 * f(x) +  -1 * f(y) > 0 )  }) })
      .expected(exactly(
            clause({      num(0) * f(x) > 0 }) 
      )))

TEST_GENERATION(basic10,
    Generation::SymmetricTest()
      .rule(new TermFactoring(testTermFactoring(Shell::Options::UnificationWithAbstraction::OFF)))
      .inputs  ({  clause({ selected(h(a, x, x1) + h(x, x, x2) + h(b, x, x3) > 0)  }) })
      .expected(exactly(
                  clause({ 2 * h(a, a, x) + h(b, a, y) > 0  }) 
                , clause({ 2 * h(b, b, y) + h(a, b, x) > 0  }) 
      )))


TEST_GENERATION(unshielded_vars_0,
    Generation::SymmetricTest()
      .inputs  ({  clause({ selected(x + a > 0)  }) })
      .expected(exactly( /* nothing */  ))
    )

TEST_GENERATION(unshielded_vars_1,
    Generation::SymmetricTest()
      .inputs  ({  clause({ selected(-x + a > 0)  }) })
      .expected(exactly( /* nothing */  ))
    )


TEST_GENERATION(unshielded_vars_2,
    Generation::SymmetricTest()
      .inputs  ({  clause({ selected(x + -a > 0)  }) })
      .expected(exactly( /* nothing */  ))
    )

TEST_GENERATION(unshielded_vars_3,
    Generation::SymmetricTest()
      .inputs  ({  clause({ selected(-x + -a > 0)  }) })
      .expected(exactly( /* nothing */  ))
    )

/////////////////////////////////////////////////////////
// UWA tests
//////////////////////////////////////

TEST_GENERATION(abstraction1_one_interp,
    Generation::SymmetricTest()
      .rule(new TermFactoring(testTermFactoring(Shell::Options::UnificationWithAbstraction::ALASCA_ONE_INTERP)))
      .inputs  ({  clause({ selected(-f(f(x) + g(a, c)) + f(f(y) + g(b, c)) > 0)   })})
      .expected(exactly(
            clause({ 0 * f(f(x) + g(a, c)) > 0, f(y) + g(b, c) != f(x) + g(a, c) })
      )))

TEST_GENERATION(abstraction1,
    Generation::SymmetricTest()
      .inputs  ({  clause({ selected(-f(f(x) + g(a, c)) + f(f(y) + g(b, c)) > 0)   })})
      .expected(exactly(
      )))



/////////////////////////////////////////////////////////
// MISC
//////////////////////////////////////

TEST_GENERATION(misc01,
    Generation::SymmetricTest()
      .inputs  ({          clause({ selected( -     x    - g(x,z) + g(-30 * y,y) > 0 ) , selected( 0 != y + z ) }) }) // { x -> -30 * x, z -> x, y -> x }
      .expected(exactly(  clause({ -(-30 * x) + 0 * g(-30 * x, x) > 0 , 0 != x + x }) )))

TEST_GENERATION(misc02,
    Generation::SymmetricTest()
      .inputs  ({              clause({ selected( -(    x  ) + 2 * g(-30 * y, z) + -g(x,y) > 0 ) , selected( 0 != z ) }) }) // { x -> -30 * x, z -> x, y -> x }
      .expected(exactly(anyOf(clause({   (-30 * x) + -1 * g(-30 * x, x) > 0          , 0 != x }),
                              clause({  -(-30 * x) +  1 * g(-30 * x, x) > 0       , 0 != x })
            ) )))

TEST_GENERATION(misc03,
    Generation::SymmetricTest()
      .inputs  ({              clause({ selected(   x0 + g(x2,x3) + g(x0,x1) > 0 ) , selected( 0 != x3 + x1 ) }) }) // { x3 -> x0, x2 -> x1 }
      .expected(exactly(anyOf(clause({   x0 +        2 * g(x0,x1) > 0 , 0 != x1 + x1 })  
                            , clause({  -x0 +       -2 * g(x0,x1) > 0 , 0 != x1 + x1 })))))

  // 51017. 0.0 != ((-3.0 * X31) + (lG132(X21,X22) + (lG145($product(18.0,X24),X25) + -(lG132(X31,X24))))) | 0.0 != (X21 + (-10.0 * X25)) <- (48) [trivial inequality removal 51016]
  // 99594. 0.0 != ((-3.0 * X0) + lG145($product(18.0,X1),X2)) | 0.0 != (X0 + (-10.0 * X2)) <- (48) [inequality term factoring 51017]

  
  

TEST_GENERATION(misc04,
    Generation::SymmetricTest()
      .inputs  ({              clause({selected( -3 * x0 + g0(x3,x4) - g0(x0,x1) + g1(18 * x1, x2) > 0 ) , selected( 0 != x0 + -10 * x2 )}) })
      .expected(exactly(       clause({-3 * x0 +       0 * g0(x0, x2)  + g1(18 * x2, x3) > 0 , 0 != x0 + -10 * x3}) )))


TEST_GENERATION(factor_only_global_max_atomic_terms_01,
    Generation::SymmetricTest()
      .inputs  ({              clause({ f(x) + f(f(y)) > 0, f(f(x)) + f(f(y)) > 0 }) })
      .expected(exactly(       clause({ f(x) + f(f(x)) > 0, 2 * f(f(x)) > 0 }) )))

TEST_GENERATION(factor_only_global_max_atomic_terms_02,
    Generation::SymmetricTest()
      .inputs  ({              clause({ f(x) + f(y) > 0, f(f(x)) > 0 }) })
      .expected(exactly(                                                       )))


TEST_GENERATION(factor_only_global_max_atomic_terms_03,
    Generation::SymmetricTest()
      .inputs  ({              clause({ f(x) + f(y) + a > 0, 2 * f(x) + b > 0 }) })
      .expected(exactly(       clause({    2 * f(x) + a > 0, 2 * f(x) + b > 0 }) )))

TEST_GENERATION(factor_only_global_max_atomic_terms_04,
    Generation::SymmetricTest()
      .inputs  ({              clause({ f(x) + f(y) + b > 0, 2 * f(x) + a > 0 }) })
      .expected(exactly(       clause({    2 * f(x) + b > 0, 2 * f(x) + a > 0 }) )))

TEST_GENERATION(factor_only_global_max_atomic_terms_05,
    Generation::SymmetricTest()
      .inputs  ({              clause({ g(x,y) + g(y,x) + b > 0, f(g(x,x)) > 0 }) })
      .expected(exactly(       /* nothing */                                     )))

/////////////////////////////////////////////////////////
// Bug fixes
//////////////////////////////////////

TEST_GENERATION(bug_01,
    Generation::SymmetricTest()
// 1 + f26(f34(f59,X0),X0) + f26(f34(f59,X1),X1) > 0 [theory normalization 1587]
// 2 * f26(f34(f59,X0),X0) + f26(f34(f59,X0),X0) > 0 [inequality factoring 2373]
      .inputs  ({          clause({ selected(1 + f(x) + f(y) > 0)  })    })
      .expected(exactly(  clause({          1 +    2 * f(x) > 0   })   )))





TEST_GENERATION(bug_02b_one_interp,
    Generation::SymmetricTest()
      .rule(move_to_heap(testTermFactoring(Shell::Options::UnificationWithAbstraction::ALASCA_ONE_INTERP)))
      .inputs  ({   clause({ selected( -23 * x0 + g(x0, -23 * x1) + -g(x1, -23 * x2) > 0 ) })    })
      // ({x1 -> x0}, -23 * x0 != -23 * x2) = uwa( ^^^^^^^^^^^^^^,    ^^^^^^^^^^^^^^ ) (1)
      .expected(exactly(  
                               clause({ -23 * x0 +       0 * g(x0, -23 * x0)           > 0, -23 * x0 != -23 * x1 })   
          )))

TEST_GENERATION(bug_02b,
    Generation::SymmetricTest()
  // 0.0 != ((-23.0 * X24) + (lG113($product(-23.0,X22),X24) + (-(lG113($product(-23.0,X21),X22)) + lG113(X23,X21)))) | 0.0 = X23
      .inputs  ({   clause({ selected( -23 * x0 + g(x0, -23 * x1) + -g(x1, -23 * x2) > 0 ) })    })
      // ({x1 -> x0}, -23 * x0 != -23 * x2) = uwa( ^^^^^^^^^^^^^^,    ^^^^^^^^^^^^^^ ) (1)
      .expected(exactly(  
                               clause({ -23 * x0 +       0 * g(x0, -23 * x0)           > 0 })   
          )))


TEST_GENERATION(bug_02_one_interp,
    Generation::SymmetricTest()
      .rule(new TermFactoring(testTermFactoring(Shell::Options::UnificationWithAbstraction::ALASCA_ONE_INTERP)))
  // 0.0 != ((-23.0 * X24) + (lG113($product(-23.0,X22),X24) + (-(lG113($product(-23.0,X21),X22)) + lG113(X23,X21)))) | 0.0 = X23
      .inputs  ({    clause({ selected( -23 * x0 + g(-23 * x1,x0) + -g(-23 * x2, x1) > 0 ) })    })
      // ({x1 -> x0}, -23 * x0 != -23 * x2) = uwa( ^^^^^^^^^^^^^^ ,  ^^^^^^^^^^^^^^ ) 
      .expected(exactly(  
                               clause({ -23 * x0 +         0 * g(-23 * x0, x0)       > 0, -23 * x0 != -23 * x1 })   
          )))

TEST_GENERATION(bug_02,
    Generation::SymmetricTest()
      .inputs  ({    clause({ selected( -23 * x0 + g(-23 * x1,x0) + -g(-23 * x2, x1) > 0 ) })    })
      // ({x1 -> x0}, -23 * x0 != -23 * x2) = uwa( ^^^^^^^^^^^^^^ ,  ^^^^^^^^^^^^^^ ) 
      .expected(exactly(  
                               clause({ -23 * x0 +         0 * g(-23 * x0, x0)       > 0 })   
          )))

TEST_GENERATION(non_linear_tryout01,
    Generation::SymmetricTest()
      .inputs  ({    clause({ (x * a) - (a * a) != 0 })    })
      .rule(new TermFactoring(testTermFactoring(Shell::Options::UnificationWithAbstraction::ALASCA_MAIN)))
      .expected(exactly(  
           clause({ 0 * (a * a) != 0 })
          )))

TEST_GENERATION(tricky_uwa_01_one_interp,
    Generation::SymmetricTest()
    .rule(move_to_heap(testTermFactoring(Shell::Options::UnificationWithAbstraction::ALASCA_ONE_INTERP)))
      .inputs  ({    clause({     f(x) + f(f(x) + y) > 0  })    })
      .expected(exactly( clause({ 2 * f(x) > 0, f(x) + y != x }) )))

TEST_GENERATION(tricky_uwa_01,
    Generation::SymmetricTest()
      .inputs  ({    clause({     f(x) + f(f(x) + y) > 0  })    })
      .expected(exactly( clause({ 2 * f(x) > 0 }) )))

TEST_GENERATION(tricky_uwa_02,
    Generation::SymmetricTest()
      .inputs  ({    clause({     f(x) + f(f(x)) > 0  })    })
      .expected(exactly( /* nothing */ )))

TEST_GENERATION(tricky_uwa_03,
    Generation::SymmetricTest()
      .inputs  ({    clause({     f(x) + f(g(x, x + y)) > 0  })    })
      .expected(exactly( /* nothing */ )))

TEST_GENERATION(tricky_uwa_04,
    Generation::SymmetricTest()
      .inputs  ({        clause({  f(x) + f(g(x + z, x + y)) > 0  }) })
      .expected(exactly( clause({  2 * f(x) > 0, x != g(x + z, x + y)  }) )))

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
#include "Inferences/IRC/TermFactoring.hpp"
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
  DECL_VAR(x0, 0)                                                                                             \
  DECL_VAR(x1, 1)                                                                                             \
  DECL_VAR(x2, 2)                                                                                             \
  DECL_VAR(x3, 3)                                                                                             \
  DECL_VAR(x4, 4)                                                                                             \
  DECL_FUNC(f, {Num}, Num)                                                                                    \
  DECL_FUNC(g, {Num, Num}, Num)                                                                               \
  DECL_FUNC(g0, {Num, Num}, Num)                                                                              \
  DECL_FUNC(g1, {Num, Num}, Num)                                                                              \
  DECL_FUNC(h, {Num, Num, Num}, Num)                                                                          \
  DECL_CONST(a, Num)                                                                                          \
  DECL_CONST(b, Num)                                                                                          \
  DECL_CONST(c, Num)                                                                                          \
  DECL_PRED(p, {Num})                                                                                         \
  DECL_PRED(r, {Num,Num})                                                                                     \

#define MY_SYNTAX_SUGAR SUGAR(Rat)


TermFactoring testTermFactoring(
    Options::UnificationWithAbstraction uwa = Options::UnificationWithAbstraction::IRC1
    )
{ 
  return TermFactoring(testIrcState(uwa));
}

REGISTER_GEN_TESTER(Test::Generation::GenerationTester<TermFactoring>(testTermFactoring()))

/////////////////////////////////////////////////////////
// Basic tests
//////////////////////////////////////

TEST_GENERATION(basic01a,
    Generation::SymmetricTest()
      .inputs  ({  clause({selected( 3 * g(a, x) + 2 * g(y, b) > 0 ), p(x) }) })
      .expected(exactly(
          /* nothing because uninterpreted stuff is bigger */
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION(basic01b,
    Generation::SymmetricTest()
      .inputs  ({  clause({selected( 3 * g(a, x) + 2 * g(y, b) > 0 ), f(x)  == 1 }) })
      .expected(exactly(
            clause({ 5 * g(a,b) > 0, f(b) == 1  })
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION(basic02,
    Generation::SymmetricTest()
      .inputs  ({  clause({ selected( 1 * f(x) +  -1 * f(a) > 0 )  }) })
      .expected(exactly(
            clause({      num(0) > 0 }) 
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION(basic03,
    Generation::SymmetricTest()
      .inputs  ({  clause({ selected( 1 * f(x) +  -1 * f(y) > 0 )  }) })
      .expected(exactly(
            clause({      num(0) > 0 }) 
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION(basic04,
    Generation::SymmetricTest()
      .rule(new TermFactoring(testTermFactoring(Shell::Options::UnificationWithAbstraction::OFF)))
      .inputs  ({  clause({ selected(h(a, x, x1) + h(x, x, x2) + h(b, x, x3) > 0)  }) })
      .expected(exactly(
                  clause({ 2 * h(a, a, x) + h(b, a, y) > 0  }) 
                , clause({ 2 * h(b, b, y) + h(a, b, x) > 0  }) 
      ))
      .premiseRedundant(false)
    )

/////////////////////////////////////////////////////////
// UWA tests
//////////////////////////////////////

TEST_GENERATION(abstraction1,
    Generation::SymmetricTest()
      .inputs  ({  clause({ selected(-f(f(x) + g(a, c)) + f(f(y) + g(b, c)) > 0)   })})
      .expected(exactly(
            clause({ num(0) > 0, f(y) + g(b, c) != f(x) + g(a, c) })
      ))
      .premiseRedundant(false)
    )



/////////////////////////////////////////////////////////
// MISC
//////////////////////////////////////

TEST_GENERATION(misc01,
    Generation::SymmetricTest()
  // 0 != (-(x) + (-(g(x,z)) + g(-30 * y,y))) | 0 != (y + z) { x -> -30 * y, z -> y }
  // 0 != -((-30 * y)) | 0 != (y + y) 
      .inputs  ({          clause({ -     x    - g(x,z) + g(-30 * y,y) > 0 , 0 != y + z }) }) // { x -> -30 * x, z -> x, y -> x }
      .expected(exactly(  clause({ -(-30 * x)                         > 0 , 0 != x + x }) ))
      .premiseRedundant(false)
    )

TEST_GENERATION(misc02,
    Generation::SymmetricTest()
      .inputs  ({              clause({ 0 != -(    x  ) + 2 * g(-30 * y, z) + -g(x,y) , 0 != z }) }) // { x -> -30 * x, z -> x, y -> x }
      .expected(exactly(anyOf(clause({ 0 !=  (-30 * x) +    -g(-30 * x, x)           , 0 != x }),
                              clause({ 0 != -(-30 * x) +     g(-30 * x, x)           , 0 != x })
            ) ))
      .premiseRedundant(false)
    )

TEST_GENERATION(misc03,
    Generation::SymmetricTest()
      .inputs  ({              clause({ 0 !=  x0 + g(x2,x3) + g(x0,x1) , 0 != x3 + x1 }) }) // { x3 -> x0, x2 -> x1 }
      .expected(exactly(anyOf(clause({ 0 !=  x0 +        2 * g(x0,x1) , 0 != x1 + x1 })  
                            , clause({ 0 != -x0 +       -2 * g(x0,x1) , 0 != x1 + x1 }))))
      .premiseRedundant(false)
    )

  // 51017. 0.0 != ((-3.0 * X31) + (lG132(X21,X22) + (lG145($product(18.0,X24),X25) + -(lG132(X31,X24))))) | 0.0 != (X21 + (-10.0 * X25)) <- (48) [trivial inequality removal 51016]
  // 99594. 0.0 != ((-3.0 * X0) + lG145($product(18.0,X1),X2)) | 0.0 != (X0 + (-10.0 * X2)) <- (48) [inequality term factoring 51017]

  
  

TEST_GENERATION(misc04,
    Generation::SymmetricTest()
      .inputs  ({              clause({-3 * x0 + g0(x3,x4) - g0(x0,x1) + g1(18 * x1, x2) > 0 , 0 != x0 + -10 * x2})  })
      .expected(exactly(      clause({-3 * x0                         + g1(18 * x1, x2) > 0 , 0 != x0 + -10 * x2}) ))
      .premiseRedundant(false)
    )

/////////////////////////////////////////////////////////
// Bug fixes
//////////////////////////////////////

TEST_GENERATION(bug_01,
    Generation::SymmetricTest()
// 1 + f26(f34(f59,X0),X0) + f26(f34(f59,X1),X1) > 0 [theory normalization 1587]
// 2 * f26(f34(f59,X0),X0) + f26(f34(f59,X0),X0) > 0 [inequality factoring 2373]
      .inputs  ({          clause({ selected(1 + f(x) + f(y) > 0)  })    })
      .expected(exactly(  clause({          1 +    2 * f(x) > 0   })   ))
      .premiseRedundant(false)
    )




// TEST_GENERATION(bug_02,
//     Generation::SymmetricTest()
//   // 0.0 != ((-23.0 * X24) + (lG113($product(-23.0,X22),X24) + (-(lG113($product(-23.0,X21),X22)) + lG113(X23,X21)))) | 0.0 = X23
//       .inputs  ({          clause({ -23 * x0 + g(-23 * x1,x0) + -g(-23 * x2, x1) + g(x3, x2) > 0 })    })
//       // ({x1 -> x0}, -23 * x0 != -23 * x2) = uwa( ^^^^^^^^^^^^^^ ,  ^^^^^^^^^^^^^^ ) (1)
//       // ({x3 -> -23 * x1, x2 -> x1}, {})   =                   uwa( ^^^^^^^^^^^^^^ ,  ^^^^^^^^^) (2)
//       // ({x3 -> -23 * x1, x2 -> x0}, {})   = uwa( ^^^^^^^^^^^^^^ ,                    ^^^^^^^^^) (3)
//       .expected(exactly(  
//      /* (1) */            clause({ -23 * x0                                     + g(x3, x2) > 0, -23 * x0 != -23 * x2 })   
//      /* (2) */          , clause({ -23 * x0 + g(-23 * x1,x0)                                > 0 })    
//      /* (3) */          , clause({ -23 * x0 + 2* g(-23 * x1,x0) + -g(-23 * x0, x1)          > 0 })
//           ))
//       .premiseRedundant(false)
//     )


TEST_GENERATION(bug_02b,
    Generation::SymmetricTest()
  // 0.0 != ((-23.0 * X24) + (lG113($product(-23.0,X22),X24) + (-(lG113($product(-23.0,X21),X22)) + lG113(X23,X21)))) | 0.0 = X23
      .inputs  ({               clause({ -23 * x0 + g(x0, -23 * x1) + -g(x1, -23 * x2) > 0 })    })
      // ({x1 -> x0}, -23 * x0 != -23 * x2) = uwa( ^^^^^^^^^^^^^^,    ^^^^^^^^^^^^^^ ) (1)
      .expected(exactly(  
     /* (1) */                 clause({ -23 * x0                                     > 0, -23 * x0 != -23 * x1 })   
          ))
      .premiseRedundant(false)
    )


TEST_GENERATION(bug_02,
    Generation::SymmetricTest()
  // 0.0 != ((-23.0 * X24) + (lG113($product(-23.0,X22),X24) + (-(lG113($product(-23.0,X21),X22)) + lG113(X23,X21)))) | 0.0 = X23
      .inputs  ({               clause({ -23 * x0 + g(-23 * x1,x0) + -g(-23 * x2, x1) > 0 })    })
      // ({x1 -> x0}, -23 * x0 != -23 * x2) = uwa( ^^^^^^^^^^^^^^ ,  ^^^^^^^^^^^^^^ ) 
      .expected(exactly(  
                               clause({ -23 * x0                                     > 0, -23 * x0 != -23 * x1 })   
          ))
      .premiseRedundant(false)
    )

  //  clause({ -23 * x0 + g(-23 * x1,x0) + -g(-23 * x2, x1) > 0 })
  // uwa = ⟨{X2/0 -> X1, X1/0 -> X0, }, [(-23/1 * X0) != (-23/1 * X1)]⟩
  //  clause({ -23 * x0 > 0, -23 * x0 != -23 * x1 })

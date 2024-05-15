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
#include "Inferences/LASCA/IsIntFactoring.hpp"
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
using namespace Inferences::LASCA;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// TEST CASES 
/////////////////////////////////////

#define SUGAR(Num)                                                                                  \
  NUMBER_SUGAR(Num)                                                                                 \
  DECL_DEFAULT_VARS                                                                                 \
  DECL_VAR(x0,0)                                                                                    \
  DECL_VAR(x1,1)                                                                                    \
  DECL_VAR(x2,2)                                                                                    \
  DECL_VAR(x3,3)                                                                                    \
  DECL_VAR(x4,4)                                                                                    \
  DECL_CONST(a, Num)                                                                                \
  DECL_CONST(b, Num)                                                                                \
  DECL_CONST(c, Num)                                                                                \
  DECL_FUNC(f, {Num}, Num)                                                                          \
  DECL_FUNC(ff, {Num}, Num)                                                                         \
  DECL_FUNC(fff, {Num}, Num)                                                                        \
  DECL_FUNC(g, {Num, Num}, Num)                                                                     \
  DECL_FUNC(g0, {Num, Num}, Num)                                                                    \
  DECL_FUNC(g1, {Num, Num}, Num)                                                                    \
  DECL_PRED(r, {Num,Num})                                                                           \

#define MY_SYNTAX_SUGAR SUGAR(Rat)

IsIntFactoring testIsIntFactoring(
    Ordering* ordering = nullptr,
    bool strongNorm = false,
    Options::UnificationWithAbstraction uwa = Options::UnificationWithAbstraction::LPAR_MAIN
    )
{ return IsIntFactoring(testLascaState(uwa, strongNorm, ordering)); }

template<class A> A* heap(A&& a) { return new A(std::move(a)); }

REGISTER_GEN_TESTER(Test::Generation::GenerationTester<IsIntFactoring>(testIsIntFactoring()))

/////////////////////////////////////////////////////////
// Basic tests
//////////////////////////////////////

TEST_GENERATION(basic00,
    Generation::SymmetricTest()
      .inputs  ({  clause({isInt( 3 * f(x) + x ), isInt(4 * f(x) + x)   }) })
      .expected(exactly(
          // nothing
      ))
    )

TEST_GENERATION(basic01,
    Generation::SymmetricTest()
      .inputs  ({  clause({ isInt( 2 * f(x) + x ), isInt(4 * f(x) + x)   }) })
      .expected(exactly(
                   clause({ isInt( 2 * f(x) + x ), ~isInt(x + -2 * x)   })
      ))
    )

TEST_GENERATION(basic02,
    Generation::SymmetricTest()
      .inputs  ({  clause({ isInt(4 * f(x) + x  ), isInt( 2 * f(x) + x )  }) })
      .expected(exactly(
                   clause({ isInt( 2 * f(x) + x ), ~isInt(x + -2 * x)   })
      ))
    )

TEST_GENERATION(basic03,
    Generation::SymmetricTest()
      .inputs  ({  clause({ isInt(-2 * f(x) - x  ), isInt( 2 * f(x) + x )  }) })
      .expected(exactly(anyOf(
                   clause({ isInt( 2 * f(x) + x ), ~isInt(x - x)   })
                 , clause({ isInt(-2 * f(x) - x ), ~isInt(x - x)   })
      )))
    )



TEST_GENERATION(basic04a,
    Generation::SymmetricTest()
      .inputs  ({  clause({ isInt(-4 * f(x) + x  ), isInt( 2 * f(x) + x )  }) })
      .expected(exactly(
                   clause({ isInt(  2 * f(x) + x ), ~isInt(x + 2 * x)   })
      ))
    )

TEST_GENERATION(basic04b,
    Generation::SymmetricTest()
      .inputs  ({  clause({ isInt( 4 * f(x) - x  ), isInt( 2 * f(x) + x )  }) })
      .expected(exactly(anyOf(
                   clause({ isInt(  2 * f(x) + x ), ~isInt( x +  2 * x)   })
                 , clause({ isInt(  2 * f(x) + x ), ~isInt(-x + -2 * x)   })
      )))
    )

TEST_GENERATION(basic04c,
    Generation::SymmetricTest()
      .inputs  ({  clause({ isInt( 4 * f(x) - x  ), isInt( -2 * f(x) - x )  }) })
      .expected(exactly(anyOf(
                 clause({ isInt(  -2 * f(x) - x ), ~isInt( x +  2 * x)   })
               , clause({ isInt(  -2 * f(x) - x ), ~isInt(-x + -2 * x)   })
      )))
    )

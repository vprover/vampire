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
#include "Inferences/LASCA/IsIntResolution.hpp"
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
  DECL_VAR(x0, 0)                                                                                   \
  DECL_VAR(x1, 1)                                                                                   \
  DECL_VAR(x2, 2)                                                                                   \
  DECL_VAR(x3, 3)                                                                                   \
  DECL_VAR(x4, 4)                                                                                   \
  DECL_VAR(x5, 5)                                                                                   \
  DECL_VAR(x6, 6)                                                                                   \
  DECL_VAR(x7, 7)                                                                                   \
  DECL_VAR(x8, 8)                                                                                   \
  DECL_VAR(x9, 9)                                                                                   \
  DECL_VAR(x10, 10)                                                                                 \
  DECL_VAR(x11, 11)                                                                                 \
  DECL_VAR(x12, 12)                                                                                 \
  DECL_VAR(x13, 13)                                                                                 \
  DECL_VAR(x14, 14)                                                                                 \
  DECL_VAR(x15, 15)                                                                                 \
  DECL_VAR(x16, 16)                                                                                 \
  DECL_VAR(x17, 17)                                                                                 \
  DECL_VAR(x18, 18)                                                                                 \
  DECL_VAR(x19, 19)                                                                                 \
  DECL_VAR(x20, 20)                                                                                 \
  DECL_VAR(x21, 21)                                                                                 \
  DECL_VAR(x22, 22)                                                                                 \
  DECL_VAR(x23, 23)                                                                                 \
  DECL_VAR(x24, 24)                                                                                 \
  DECL_VAR(x25, 25)                                                                                 \
  DECL_VAR(x26, 26)                                                                                 \
  DECL_VAR(x27, 27)                                                                                 \
  DECL_VAR(x28, 28)                                                                                 \
  DECL_VAR(x29, 29)                                                                                 \
  DECL_FUNC(f, {Num}, Num)                                                                          \
  DECL_FUNC(g, {Num, Num}, Num)                                                                     \
  DECL_CONST(a, Num)                                                                                \
  DECL_CONST(a0, Num)                                                                               \
  DECL_CONST(a1, Num)                                                                               \
  DECL_CONST(a2, Num)                                                                               \
  DECL_CONST(a3, Num)                                                                               \
  DECL_CONST(b, Num)                                                                                \
  DECL_CONST(c, Num)                                                                                \
  DECL_PRED(r, {Num,Num})                                                                           \
  DECL_SORT(srt)                                                                                    \
  DECL_CONST(au, srt)                                                                               \
  DECL_CONST(bu, srt)                                                                               \
  DECL_FUNC(fu, {Num}, srt)                                                                         \
  DECL_FUNC(fn, {srt}, Num)                                                                         \
  DECL_CONST(delta, Num)                                                                            \
  DECL_FUNC(gg, {Num}, Num)                                                                         \
  DECL_FUNC(ff, {Num}, Num)                                                                         \
  DECL_FUNC(ab, {Num}, Num)                                                                         \
  DECL_FUNC(skx, {Num}, Num)                                                                         \

#define MY_SYNTAX_SUGAR SUGAR(Rat)

#define UWA_MODE Options::UnificationWithAbstraction::LASCA1

auto idxIsIntResolution(
   Options::UnificationWithAbstraction uwa = Options::UnificationWithAbstraction::LASCA1
    ) { 
  return Stack<std::function<Indexing::Index*()>>{
    [=]() { return new LascaIndex<IsIntResolution::Lhs>(uwa); },
    [=]() { return new LascaIndex<IsIntResolution::Rhs>(uwa); },
  }; 
}

IsIntResolution testIsIntResolution(
   Options::UnificationWithAbstraction uwa = Options::UnificationWithAbstraction::LASCA1
    ) 
{ return IsIntResolution(testLascaState(uwa)); }


template<class Rule> 
class LascaGenerationTester : public Test::Generation::GenerationTester<Rule>
{
 public:
  LascaGenerationTester(Rule r) : Test::Generation::GenerationTester<Rule>(std::move(r)) { }

};


REGISTER_GEN_TESTER(LascaGenerationTester<IsIntResolution>(testIsIntResolution()))

/////////////////////////////////////////////////////////
// Basic tests
//////////////////////////////////////

TEST_GENERATION(basic01,
    Generation::SymmetricTest()
      .indices(idxIsIntResolution())
      .inputs  ({ clause({ selected(  isInt(f(a)) ) }) 
               ,  clause({ selected( ~isInt(f(x)) ) }) })
      .expected(exactly( ///////////////////////////////////////////////////////
                  clause({ ~isInt(0)  })
      ))
    )

TEST_GENERATION(basic02,
    Generation::SymmetricTest()
      .indices(idxIsIntResolution())
      .inputs  ({ clause({ selected(  isInt(f(a)) ) }) 
               ,  clause({ selected(  isInt(f(x)) ) }) })
      .expected(exactly( ///////////////////////////////////////////////////////
                  clause({ selected( isInt(0) )  })
      ))
    )

TEST_GENERATION(basic03,
    Generation::SymmetricTest()
      .indices(idxIsIntResolution())
      .inputs  ({ clause({ selected(  isInt(f(a) + frac(1,2)) ) }) 
               ,  clause({ selected(  isInt(f(x)) ) }) })
      .expected(exactly( ///////////////////////////////////////////////////////
                  clause({ selected( isInt(-frac(1,2)) )  })
      ))
    )

TEST_GENERATION(basic04,
    Generation::SymmetricTest()
      .indices(idxIsIntResolution())
      .inputs  ({ clause({ selected(  isInt(f(a) + frac(1,2)) ) }) 
               ,  clause({ selected(  ~isInt(f(x)) ) }) })
      .expected(exactly( ///////////////////////////////////////////////////////
                  clause({ selected( ~isInt(-frac(1,2)) )  })
      ))
    )

TEST_GENERATION(basic05,
    Generation::SymmetricTest()
      .indices(idxIsIntResolution())
      .inputs  ({ clause({ selected(  isInt(f(a) + a + frac(1,2)) ) }) 
               ,  clause({ selected( ~isInt(f(x) + 2)             ) }) })
      .expected(exactly( ///////////////////////////////////////////////////////
                  clause({ selected( ~isInt(2 - (a + frac(1,2))) )  })
      ))
    )

TEST_GENERATION(factors01,
    Generation::SymmetricTest()
      .indices(idxIsIntResolution())
      .inputs  ({ clause({ selected(  isInt(frac(1,2) * f(a) + a) ) }) 
               ,  clause({ selected(  isInt(frac(1,2) * f(x) + 1) ) }) })
      .expected(exactly( ///////////////////////////////////////////////////////
                  clause({ selected(  isInt(1 - a) )  })
      ))
    )

TEST_GENERATION(factors02,
    Generation::SymmetricTest()
      .indices(idxIsIntResolution())
      .inputs  ({ clause({ selected(  isInt(frac(1,2) * f(a) + a) ) }) 
               ,  clause({ selected( ~isInt(f(x) + 1) ) }) })
      .expected(exactly( ///////////////////////////////////////////////////////
                  clause({ selected( ~isInt(1 + (-2 * a)) )  })
      ))
    )

TEST_GENERATION(factors03,
    Generation::SymmetricTest()
      .indices(idxIsIntResolution())
      .inputs  ({ clause({ selected(  isInt(2 * f(x) + x) ) }) 
               ,  clause({ selected( ~isInt(f(a) + 1) ) }) })
      .expected(exactly( ///////////////////////////////////////////////////////

      ))
    )


TEST_GENERATION(factors04,
    Generation::SymmetricTest()
      .indices(idxIsIntResolution())
      .inputs  ({ clause({ selected(  isInt(frac(2,3) * f(x) + x) ) }) 
               ,  clause({ selected( ~isInt(6 * f(a) + 1) ) }) })
      .expected(exactly( ///////////////////////////////////////////////////////

      ))
    )


TEST_GENERATION(factors05,
    Generation::SymmetricTest()
      .indices(idxIsIntResolution())
      .inputs  ({ clause({ selected(  isInt(f(x) + x) ) }) 
               ,  clause({ selected( ~isInt(2 * f(a) + 1) ) }) })
      .expected(exactly( ///////////////////////////////////////////////////////
                  clause({ selected( ~isInt(1 - 2 * a) ) }) 
      ))
    )


TEST_GENERATION(factors06,
    Generation::SymmetricTest()
      .indices(idxIsIntResolution())
      .inputs  ({ clause({ selected(  isInt(f(x) + x) ) }) 
               ,  clause({ selected(  isInt(2 * f(a) + 1) ) }) })
      .expected(exactly( ///////////////////////////////////////////////////////
                  clause({ selected(  isInt(1 - 2 * a) ) }) 
      ))
    )


TEST_GENERATION(factors07,
    Generation::SymmetricTest()
      .indices(idxIsIntResolution())
      .inputs  ({ clause({ selected( ~isInt(f(x) + x) ) }) 
               ,  clause({ selected(  isInt(2 * f(a) + 1) ) }) })
      .expected(exactly( ///////////////////////////////////////////////////////
                         //nothing
      ))
    )

TEST_GENERATION(factors08,
    Generation::SymmetricTest()
      .indices(idxIsIntResolution())
      .inputs  ({ clause({ selected(  isInt(frac(2,3) * f(x) + x) ) }) 
               ,  clause({ selected( ~isInt(6 * f(a) + 1) ) }) })
      .expected(exactly( ///////////////////////////////////////////////////////
          clause({ ~isInt(1 - 9 * a) })
      ))
    )


  //;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

TEST_GENERATION(max_after_unif_01,
    Generation::SymmetricTest()
      .indices(idxIsIntResolution())
      .inputs  ({ clause({ selected(  isInt(f(x) + f(f(a))) ) }) 
               ,  clause({ selected( ~isInt(f(a) + 1) ) }) })
      .expected(exactly( ///////////////////////////////////////////////////////
                         // nothing
      ))
    )

TEST_GENERATION(max_after_unif_02,
    Generation::SymmetricTest()
      .indices(idxIsIntResolution())
      .inputs  ({ clause({ selected(  isInt(f(x) + f(a)) ) }) 
               ,  clause({ selected( ~isInt(f(a) + 1) ) }) })
      .expected(exactly( ///////////////////////////////////////////////////////
          clause({ ~isInt(1 - f(x)) })
      ))
    )


TEST_GENERATION(max_after_unif_03,
    Generation::SymmetricTest()
      .indices(idxIsIntResolution())
      .inputs  ({ clause({ selected(  isInt(f(a)) ) }) 
               ,  clause({ selected( ~isInt(f(x) + f(f(a)) + 1) ) }) })
      .expected(exactly( ///////////////////////////////////////////////////////
                         // nothing
      ))
    )

TEST_GENERATION(max_after_unif_04,
    Generation::SymmetricTest()
      .indices(idxIsIntResolution())
      .inputs  ({ clause({ selected(  isInt(f(a)) ) }) 
               ,  clause({ selected( ~isInt(f(x) + f(a) + 1) ) }) })
      .expected(exactly( ///////////////////////////////////////////////////////
          clause({ ~isInt(1 - f(x)) })
      ))
    )

TEST_GENERATION(negative_factors_01,
    Generation::SymmetricTest()
      .indices(idxIsIntResolution())
      .inputs  ({ clause({ selected(  isInt(-f(x) + f(b)) ) }) 
               ,  clause({ selected( ~isInt(f(a) + 1) ) }) })
      .expected(exactly( ///////////////////////////////////////////////////////
                  clause({ selected( ~isInt(1 + f(b)) ) })
      ))
    )


TEST_GENERATION(negative_factors_02,
    Generation::SymmetricTest()
      .indices(idxIsIntResolution())
      .inputs  ({ clause({ selected(  isInt( f(x) - f(b)) ) }) 
               ,  clause({ selected( ~isInt(f(a) + 1) ) }) })
      .expected(exactly( ///////////////////////////////////////////////////////
                  clause({ selected( ~isInt(1 + f(b)) ) })
      ))
    )


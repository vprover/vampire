/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Kernel/LASCA.hpp"
#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Indexing/TermSharing.hpp"
#include "Inferences/LASCA/InequalityStrengthening.hpp"
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

#define UWA_MODE Options::UnificationWithAbstraction::LPAR_MAIN

auto idxInequalityStrengthening(
   Options::UnificationWithAbstraction uwa = Options::UnificationWithAbstraction::LPAR_MAIN
    ) { 
  return Stack<std::function<Indexing::Index*()>>{
    [=]() { return new LascaIndex<InequalityStrengthening::Lhs>(); },
    [=]() { return new LascaIndex<InequalityStrengthening::Rhs>(); },
  }; 
}

InequalityStrengthening testInequalityStrengthening(
   Options::UnificationWithAbstraction uwa = Options::UnificationWithAbstraction::LPAR_MAIN
    ) 
{ return InequalityStrengthening(testLascaState(uwa)); }


template<class Rule> 
class LascaGenTester : public Test::Generation::GenerationTester<Rule>
{
 public:
  LascaGenTester(Rule r) : Test::Generation::GenerationTester<Rule>(std::move(r)) { }

  virtual bool eq(Kernel::Clause const* lhs, Kernel::Clause const* rhs) override
  { 
    auto toStack = [](auto cl) {
      return iterTraits(cl->iterLits())
        .flatMap([](auto l) { return arrayIter(Stack<Literal*>(*LascaState::globalState->normalizer.normalizeLiteral(l))); })
        .template collect<Stack<Literal*>>();
    };
    return TestUtils::eqModACRect(toStack(lhs), toStack(rhs)); }
};


REGISTER_GEN_TESTER(LascaGenTester<InequalityStrengthening>(testInequalityStrengthening()))

/////////////////////////////////////////////////////////
// Basic tests
//////////////////////////////////////

TEST_GENERATION(basic01,
    Generation::SymmetricTest()
      .indices(idxInequalityStrengthening())
      .inputs  ({ clause({            isInt(f(a))    }) 
               ,  clause({                  f(x) > 0 }) })
      .expected(exactly( ///////////////////////////////////////////////////////
                  clause({ f(a) - 1 >= 0 , ~isInt(0)  })
      ))
    )


TEST_GENERATION(basic02,
    Generation::SymmetricTest()
      .indices(idxInequalityStrengthening())
      .inputs  ({ clause({            isInt(f(a))    }) 
               ,  clause({                  2 * f(x) > 0 }) })
      .expected(exactly( ///////////////////////////////////////////////////////
                  clause({ 2 * f(a) - 2 >= 0 , ~isInt(0)  })
      ))
    )

TEST_GENERATION(basic03,
    Generation::SymmetricTest()
      .indices(idxInequalityStrengthening())
      .inputs  ({ clause({            isInt(frac(1,2) * f(a))    }) 
               ,  clause({                  f(x) > 0 }) })
      .expected(exactly( ///////////////////////////////////////////////////////
                  clause({ f(a) - 2 >= 0 , ~isInt(0)  })
      ))
    )

TEST_GENERATION(basic04,
    Generation::SymmetricTest()
      .indices(idxInequalityStrengthening())
      .inputs  ({ clause({            isInt(2 * f(a))    }) 
               ,  clause({                  f(x) > 0 }) })
      .expected(exactly( ///////////////////////////////////////////////////////
                  clause({ 2 * f(a) - 1 >= 0 , ~isInt(0)  })
          
      ))
    )

TEST_GENERATION(basic04b,
    Generation::SymmetricTest()
      .indices(idxInequalityStrengthening())
      .inputs  ({ clause({            isInt(f(a))    }) 
               ,  clause({                  frac(1,2) * f(x) > 0 }) })
      .expected(exactly( ///////////////////////////////////////////////////////
                  clause({ frac(1,2) * f(a) - frac(1,2) >= 0 , ~isInt(0)  })
          
      ))
    )

TEST_GENERATION(basic05,
    Generation::SymmetricTest()
      .indices(idxInequalityStrengthening())
      .inputs  ({ clause({            isInt(frac(1,2) * f(a))    }) 
               ,  clause({                  f(x) > 0 }) })
      .expected(exactly( ///////////////////////////////////////////////////////
                  clause({ f(a) - 2 >= 0 , ~isInt(0)  })
      ))
    )


TEST_GENERATION(basic0101,
    Generation::SymmetricTest()
      .indices(idxInequalityStrengthening())
      .inputs  ({ clause({            isInt(f(a) + a)    }) 
               ,  clause({                  f(x) + b > 0 }) })
      .expected(exactly( ///////////////////////////////////////////////////////
                  clause({ f(a) + b - 1 >= 0 , ~isInt(b - a)  })
      ))
    )

TEST_GENERATION(basic0102,
    Generation::SymmetricTest()
      .indices(idxInequalityStrengthening())
      .inputs  ({ clause({            isInt(f(a) + a)    }) 
               ,  clause({                  2 * f(x) + b > 0 }) })
      .expected(exactly( ///////////////////////////////////////////////////////
                  clause({ 2 * f(a) + b - 2 >= 0 , ~isInt(frac(1,2) * b - a)  })
      ))
    )


TEST_GENERATION(basic0201,
    Generation::SymmetricTest()
      .indices(idxInequalityStrengthening())
      .inputs  ({ clause({            isInt(f(a) + a)    }) 
               ,  clause({                  -f(x) + b > 0 }) })
      .expected(exactly( ///////////////////////////////////////////////////////
                  clause({ -f(a) + b + 1 >= 0 , ~isInt(-b - a)  })
      ))
    )

TEST_GENERATION(basic0202,
    Generation::SymmetricTest()
      .indices(idxInequalityStrengthening())
      .inputs  ({ clause({            isInt(f(a) + a)    }) 
               ,  clause({                  -2 * f(x) + b > 0 }) })
      .expected(exactly( ///////////////////////////////////////////////////////
                  clause({ -2 * f(a) + b + 2 >= 0 , ~isInt(frac(-1,2) * b - a)  })
      ))
    )


TEST_GENERATION(basic0203,
    Generation::SymmetricTest()
      .indices(idxInequalityStrengthening())
      .inputs  ({ clause({            isInt(-f(a) + a)    }) 
               ,  clause({                  -f(x) + b > 0 }) })
      .expected(exactly( ///////////////////////////////////////////////////////
                  clause({ -f(a) + b + 1 >= 0 , ~isInt(-b + a)  })
      ))
    )

TEST_GENERATION(basic0204,
    Generation::SymmetricTest()
      .indices(idxInequalityStrengthening())
      .inputs  ({ clause({            isInt(-f(a) + a)    }) 
               ,  clause({                  -2 * f(x) + b > 0 }) })
      .expected(exactly( ///////////////////////////////////////////////////////
                  clause({ -2 * f(a) + b + 2 >= 0 , ~isInt(frac(-1,2) * b + a)  })
      ))
    )

TEST_GENERATION(basic0301,
    Generation::SymmetricTest()
      .indices(idxInequalityStrengthening())
      .inputs  ({ clause({            isInt(-f(a))    }) 
               ,  clause({                  -f(x) > 0 }) })
      .expected(exactly( ///////////////////////////////////////////////////////
                  clause({ -f(a) + 1 >= 0 , ~isInt(0)  })
      ))
    )


TEST_GENERATION(basic0302,
    Generation::SymmetricTest()
      .indices(idxInequalityStrengthening())
      .inputs  ({ clause({            isInt( f(a))    }) 
               ,  clause({                  -f(x) > 0 }) })
      .expected(exactly( ///////////////////////////////////////////////////////
                  clause({ -f(a) + 1 >= 0 , ~isInt(0)  })
      ))
    )


TEST_GENERATION(basic0303,
    Generation::SymmetricTest()
      .indices(idxInequalityStrengthening())
      .inputs  ({ clause({            isInt( f(a))    }) 
               ,  clause({                   f(x) > 0 }) })
      .expected(exactly( ///////////////////////////////////////////////////////
                  clause({  f(a) - 1 >= 0 , ~isInt(0)  })
      ))
    )


TEST_GENERATION(basic0304,
    Generation::SymmetricTest()
      .indices(idxInequalityStrengthening())
      .inputs  ({ clause({            isInt(-f(a))    }) 
               ,  clause({                   f(x) > 0 }) })
      .expected(exactly( ///////////////////////////////////////////////////////
                  clause({  f(a) - 1 >= 0 , ~isInt(0)  })
      ))
    )




  //;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

TEST_GENERATION(max_after_unif_01,
    Generation::SymmetricTest()
      .indices(idxInequalityStrengthening())
      .inputs  ({ clause({  isInt(f(x) + f(f(a))) }) 
               ,  clause({        f(a) + 1 > 0    }) })
      .expected(exactly( ///////////////////////////////////////////////////////
                         // nothing
      ))
    )

TEST_GENERATION(max_after_unif_02,
    Generation::SymmetricTest()
      .indices(idxInequalityStrengthening())
      .inputs  ({ clause({   isInt(f(x) + f(a))   }) 
               ,  clause({         f(a) + 1   > 0 }) })
      .expected(exactly( ///////////////////////////////////////////////////////
          clause({ f(a) >= 0, ~isInt(1 - f(x)) })
      ))
    )


TEST_GENERATION(max_after_unif_03,
    Generation::SymmetricTest()
      .indices(idxInequalityStrengthening())
      .inputs  ({ clause({   isInt(f(a))                   }) 
               ,  clause({         f(x) + f(f(a)) + 1  > 0 }) })
      .expected(exactly( ///////////////////////////////////////////////////////
                         // nothing
      ))
    )

TEST_GENERATION(max_after_unif_04,
    Generation::SymmetricTest()
      .indices(idxInequalityStrengthening())
      .inputs  ({ clause({ isInt(f(a))                }) 
               ,  clause({       f(x) + f(a) + 1 > 0  }) })
      .expected(exactly( ///////////////////////////////////////////////////////
          clause({ f(x) + f(a) >= 0,  ~isInt((f(x) + 1) - 0) })
      ))
    )


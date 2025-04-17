/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Kernel/ALASCA/Selection.hpp"
#include "Kernel/LookaheadLiteralSelector.hpp"
#include "Kernel/MaximalLiteralSelector.hpp"
#include "Kernel/RndLiteralSelector.hpp"
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
  DECL_FUNC(f, {Num}, Num)                                                                \
  DECL_FUNC(g, {Num}, Num)                                                                \
  DECL_FUNC(f2, {Num, Num}, Num)                                                          \
  DECL_FUNC(g2, {Num, Num}, Num)                                                          \
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
  DECL_FUNC(fnu, {Num}, srt)                                                              \
  DECL_FUNC(fun, {srt}, Num)                                                              \

#define MY_SYNTAX_SUGAR SUGAR(Rat)

REGISTER_GEN_TESTER(AlascaGenerationTester<FourierMotzkin>())

/////////////////////////////////////////////////////////
// Basic tests
//////////////////////////////////////

template<class SelectorMode>
auto asymSelectionTest() {
  auto s = testAlascaState(
      Options::UnificationWithAbstraction::ALASCA_MAIN,
      Lib::make_shared(InequalityNormalizer()),
      nullptr,
     /*uwaFixdPointIteration=*/ false,
     AlascaSelector::fromType<SelectorMode>());

  auto* rule = move_to_heap(alascaSimplRule(s, FourierMotzkin(s), ALASCA::Normalization(s)));
  return Generation::AsymmetricTest()
      .rule(rule)
      .setup([=](auto& alg) { s->selector.setLookaheadInferenceEngine(rule); });

}


TEST_GENERATION(rnd_complete_01,
    asymSelectionTest<GenericRndLiteralSelector</* complete */ true>>()
      .context ({ clause({ f(x) > 0, -a > 0   }) })
      .input   (  clause({ -f(a) > 0 }) )
      .expected(exactly( /* nothing */ ))
    )

TEST_GENERATION(rnd_complete_02,
    asymSelectionTest<GenericRndLiteralSelector</* complete */ true>>()
      .context ({ clause({ f(x) > 0, -a > 0   }) })
      .input   (  clause({ -f(a) > 0, a > 0 }) )
      .expected(exactly( /* nothing */ ))
    )

TEST_GENERATION(rnd_complete_02a,
    asymSelectionTest<GenericRndLiteralSelector</* complete */ true>>()
      .context ({ clause({ f(x) > 0, f(y) - f(a) > 0   }) })
      .input   (  clause({-f(b) > 0 }) )
      .expected(exactly( 
                  clause({           f(x) - f(a) > 0   }) 
               ,  clause({ f(x) > 0,      - f(a) > 0   }) 
          ))
    )
// in this case the global maximality of the term f(x) does not hold, so no inference is applied
TEST_GENERATION(rnd_complete_02b,
    asymSelectionTest<GenericRndLiteralSelector</* complete */ true>>()
      .context  ({ clause({ f(x) > 0, f(x) - f(a) > 0   }) })
      .input   (  clause({-f(b) > 0 }) )
      .expected(exactly(  /* nothing */ ))
    )

TEST_GENERATION(rnd_complete_03,
    asymSelectionTest<GenericRndLiteralSelector</* complete */ true>>()
      .context ({ clause({ a - b > 0 }) })
      .input   (  clause({ b - a > 0 }) )
      .expected(exactly(
                  clause({ num(0) > 0 }) 
          ))
    )

TEST_GENERATION(lookahead_01_complete,
    asymSelectionTest<GenericLookaheadLiteralSelector</* complete */ true>>()
      .context ({ clause({ f(a) + a0 > 0 })
               ,  clause({ f(b) + a0 > 0 }) ,  clause({ f(b) + a1 > 0 }),  clause({ f(b) + a2 > 0 })  
               ,  clause({ f(c) + a0 > 0 }) ,  clause({ f(c) + a1 > 0 }) 
               })
      .input   (  clause({ -f(a) > 0, -f(b) > 0, -f(c) > 0 })  )
      .expected(exactly(
                  clause({ -f(b) > 0, -f(c) > 0, a0 > 0 }) 
          ))
      )


TEST_GENERATION(lookahead_01_incomplete,
    asymSelectionTest<GenericLookaheadLiteralSelector</* complete */ false>>()
      .context ({ clause({ f(a) + a0 > 0 })
               ,  clause({ f(b) + a0 > 0 }) ,  clause({ f(b) + a1 > 0 }),  clause({ f(b) + a2 > 0 })  
               ,  clause({ f(c) + a0 > 0 }) ,  clause({ f(c) + a1 > 0 }) 
               })
      .input   (  clause({ -f(a) > 0, -f(b) > 0, -f(c) > 0 }) )
      .expected(exactly(
                  clause({ -f(b) > 0, -f(c) > 0, a0 > 0 }) 
          ))
      )

TEST_GENERATION(lookahead_02_complete,
    asymSelectionTest<GenericLookaheadLiteralSelector</* complete */ true>>()
      .context ({ clause({ -f(a) + a0 > 0 })
               ,  clause({ -f(b) + a0 > 0 }) ,  clause({ -f(b) + a1 > 0 }),  clause({ -f(b) + a2 > 0 })  
               ,  clause({ -f(c) + a0 > 0 }) ,  clause({ -f(c) + a1 > 0 }) 
               })
      .input   (  clause({ f(a) > 0, f(b) > 0, f(c) > 0 }) )
      .expected(exactly(
                  clause({  f(a) > 0,  f(b) > 0, a0 > 0 }) 
                , clause({  f(a) > 0,  f(b) > 0, a1 > 0 }) 
          ))
    )

TEST_GENERATION(lookahead_02_incomplete,
    asymSelectionTest<GenericLookaheadLiteralSelector</* complete */ false>>()
      .context ({ clause({ -f(a) + a0 > 0 })
               ,  clause({ -f(b) + a0 > 0 }) ,  clause({ -f(b) + a1 > 0 }),  clause({ -f(b) + a2 > 0 })  
               ,  clause({ -f(c) + a0 > 0 }) ,  clause({ -f(c) + a1 > 0 }) 
               })
      .input   (  clause({ f(a) > 0, f(b) > 0, f(c) > 0 }) )
      .expected(exactly(
                  clause({  f(b) > 0,  f(c) > 0, a0 > 0 }) 
          ))
    )

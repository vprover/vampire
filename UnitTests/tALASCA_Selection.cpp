/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Debug/Assertion.hpp"
#include "Inferences/ALASCA/IntegerFourierMotzkin.hpp"
#include "Inferences/BinaryResolution.hpp"
#include "Kernel/ALASCA/Selection.hpp"
#include "Kernel/BestLiteralSelector.hpp"
#include "Kernel/LookaheadLiteralSelector.hpp"
#include "Kernel/MaximalLiteralSelector.hpp"
#include "Kernel/RndLiteralSelector.hpp"
#include "Shell/Options.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Lib/STL.hpp"
#include "Inferences/ALASCA/FourierMotzkin.hpp"
#include "Inferences/ALASCA/TermFactoring.hpp"
#include "Inferences/ALASCA/Superposition.hpp"

#include "Test/SyntaxSugar.hpp"
#include "Test/AlascaTestUtils.hpp"
#include "Test/GenerationTester.hpp"
#include <initializer_list>

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
  DECL_FUNC(f3, {Num, Num, Num}, Num)                                                     \
  DECL_FUNC(g2, {Num, Num}, Num)                                                          \
  DECL_CONST(a, Num)                                                                      \
  DECL_CONST(a0, Num)                                                                     \
  DECL_CONST(a1, Num)                                                                     \
  DECL_CONST(a2, Num)                                                                     \
  DECL_CONST(a3, Num)                                                                     \
  DECL_CONST(b, Num)                                                                      \
  DECL_CONST(c, Num)                                                                      \
  DECL_PRED(r, {Num,Num})                                                                 \
  DECL_PRED(p, {Num})                                                                     \
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

template<class SelectorMode, class... Rules>
auto asymSelectionTest() {
  auto s = testAlascaState(
      Options::UnificationWithAbstraction::ALASCA_MAIN,
      Lib::make_shared(InequalityNormalizer()),
      nullptr,
     /*uwaFixdPointIteration=*/ false,
     LiteralSelectors::selectorMode<SelectorMode>());

  auto rule = new CompositeSGI();
  TypeList::List<Rules...>::forEach([&](auto token) {
      rule->push(new TypeList::TokenType<decltype(token)>(s));
  });
  // auto* rule = move_to_heap(alascaSimplRule(s, FourierMotzkin(s), ALASCA::Normalization(s)));
  return Generation::AsymmetricTest()
      .rule(rule)
      .setup([=](auto& alg) { s->selector.setLookaheadInferenceEngine(rule); });

}



TEST_GENERATION(rnd_complete_01,
    asymSelectionTest<GenericRndLiteralSelector</* complete */ true>, FourierMotzkin>()
      .context ({ clause({ f(x) > 0, -a > 0   }) })
      .input   (  clause({ -f(a) > 0 }) )
      .expected(exactly( /* nothing */ ))
    )

TEST_GENERATION(rnd_complete_02,
    asymSelectionTest<GenericRndLiteralSelector</* complete */ true>, FourierMotzkin>()
      .context ({ clause({ f(x) > 0, -a > 0   }) })
      .input   (  clause({ -f(a) > 0, a > 0 }) )
      .expected(exactly( /* nothing */ ))
    )

TEST_GENERATION(rnd_complete_02a,
    asymSelectionTest<GenericRndLiteralSelector</* complete */ true>, FourierMotzkin>()
      .context ({ clause({ f(x) > 0, f(y) - f(a) > 0   }) })
      .input   (  clause({-f(b) > 0 }) )
      .expected(exactly( 
                  clause({           f(x) - f(a) > 0   }) 
               ,  clause({ f(x) > 0,      - f(a) > 0   }) 
          ))
    )

TEST_GENERATION(rnd_complete_03,
    asymSelectionTest<GenericRndLiteralSelector</* complete */ true>, FourierMotzkin>()
      .context ({ clause({ a - b > 0 }) })
      .input   (  clause({ b - a > 0 }) )
      .expected(exactly(
                  clause({ num(0) > 0 }) 
          ))
    )

TEST_GENERATION(rnd_complete_04,
    asymSelectionTest<GenericRndLiteralSelector</* complete */ true>, TermFactoring>()
      // .context ({})
      .input   (clause({ f(x) - f(y) > 0, -f(z) - f(b) > 0   }))
      .expected(exactly( clause({ f(x) - f(y) > 0, -2 * f(b) > 0   }) ))
    )

TEST_GENERATION(lookahead_01_complete,
    asymSelectionTest<GenericLookaheadLiteralSelector</* complete */ true>, FourierMotzkin>()
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
    asymSelectionTest<GenericLookaheadLiteralSelector</* complete */ false>, FourierMotzkin>()
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
    asymSelectionTest<GenericLookaheadLiteralSelector</* complete */ true>, FourierMotzkin>()
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
    asymSelectionTest<GenericLookaheadLiteralSelector</* complete */ false>, FourierMotzkin>()
      .context ({ clause({ -f(a) + a0 > 0 })
               ,  clause({ -f(b) + a0 > 0 }) ,  clause({ -f(b) + a1 > 0 }),  clause({ -f(b) + a2 > 0 })  
               ,  clause({ -f(c) + a0 > 0 }) ,  clause({ -f(c) + a1 > 0 }) 
               })
      .input   (  clause({ f(a) > 0, f(b) > 0, f(c) > 0 }) )
      .expected(exactly(
                  clause({  f(b) > 0,  f(c) > 0, a0 > 0 }) 
          ))
    )

TEST_GENERATION(lookahead_03,
    asymSelectionTest<GenericLookaheadLiteralSelector</* complete */ false>, FourierMotzkin>()
      .context ({ clause({ -f(a) + a0 > 0 })
               ,  clause({ -g(b) + a0 > 0 }) ,  clause({ -g(b) + a1 > 0 }),  clause({ -g(b) + a2 > 0 })  
               })
      .input   (  clause({ f(x) > 0, g(y) > 0 }) )
      .expected(exactly(
                  clause({  g(x) > 0, a0 > 0 }) 
          ))
    )

TEST_GENERATION(lookahead_04_with_sup,
    asymSelectionTest<GenericLookaheadLiteralSelector</* complete */ false>, FourierMotzkin, ALASCA::Superposition>()
      .context ({ clause({ -f(a) + a0 > 0 })
               ,  clause({ -g(b) + a0 > 0 }) ,  clause({ -g(b) + a1 > 0 }),  clause({ -g(b) + a2 > 0 })  
               })
      .input   (  clause({ f(x) > 0, g(y) == 0 }) )
      .expected(exactly(
                  clause({  g(x) == 0, a0 > 0 }) 
          ))
    )

TEST_GENERATION(lookahead_04_with_sup_2,
    asymSelectionTest<GenericLookaheadLiteralSelector</* complete */ false>, FourierMotzkin, ALASCA::Superposition>()
      .context ({ clause({ -f(a) + a0 > 0 }) ,  clause({ -f(b) + a0 > 0 })
               ,  clause({ -g(b) + a0 > 0 }) ,  clause({ -g(b) + a1 > 0 }),  clause({ -g(b) + a2 > 0 })  
               })
      .input   (  clause({ f(x) > 0, g(y) == 0, f(a) == 0 }) )
      .expected(exactly(
                  clause({  f(x) > 0, g(y) == 0, a0 > 0 }) 
          ))
    )


TEST_GENERATION(lookahead_04_no_sup,
    asymSelectionTest<GenericLookaheadLiteralSelector</* complete */ false>, FourierMotzkin>()
      .context ({ clause({ -f(a) + a0 > 0 })
               ,  clause({ -g(b) + a0 > 0 }) ,  clause({ -g(b) + a1 > 0 }),  clause({ -g(b) + a2 > 0 })  
               })
      .input   (  clause({ f(x) > 0, g(y) == 0 }) )
      .expected(exactly(
          /* nothing */
          ))
    )

TEST_GENERATION(lookahead_05,
    asymSelectionTest<GenericLookaheadLiteralSelector</* complete */ false>, FourierMotzkin, IntegerFourierMotzkin<RatTraits>>()
      .context ({ clause({ -f(a) + a0 > 0 })
               ,  clause({ -g(b) + a0 > 0 }) ,  clause({ -g(b) + a1 > 0 }),  clause({ -g(b) + a2 > 0 })  
               })
      .input   (  clause({ f(x) > 0, g(y) > 0 }) )
      .expected(exactly(
                  clause({  g(x) > 0, a0 > 0 }) 
          ))
    )

TEST_FUN(best_01_alasca) {
  __ALLOW_UNUSED(
    SUGAR(Rat)
  )


  using namespace LiteralComparators;
  
  using SelectorMode = CompleteBestLiteralSelector<
     LiteralSelectors::AlascaComparator
    >;
  auto state = testAlascaState(
      Options::UnificationWithAbstraction::ALASCA_MAIN,
      Lib::make_shared(InequalityNormalizer()),
      nullptr,
     /*uwaFixdPointIteration=*/ false,
     LiteralSelectors::selectorMode<SelectorMode>());


  auto check = [&state](Clause* cl, Stack<Literal*> expected) {
    expected.sort();

    auto sel = state->selected(cl)
      .map([](auto s) { return s.literal(); })
      .collectStack()
      .sorted();


    if (sel == expected) {
      std::cout << "[ OK ] " << *cl << std::endl;
    } else {
      std::cout << "[ FAIL ] " << *cl << std::endl;
      std::cout << "[   is ] " << pretty(sel) << std::endl;
      std::cout << "[  exp ] " << pretty(expected) << std::endl;
      exit(-1);
    }
  };
  check(clause({ ~p(x), -f(a) >= 0 }), {-f(a) >= 0});
  check(clause({ ~p(a), -a >= 0 }), { ~p(a) });
  check(clause({ ~p(a), -f(x) >= 0 }), { ~p(a) });
  check(clause({ -a > 0, -f(a) > 0 }), { -f(a) > 0 });
  check(clause({ -f2(x,y) > 0, -f2(x, x) > 0 }), { -f2(x,x) > 0 });
  check(clause({ -f2(a,b) > 0, -f2(x, x) > 0 }), { -f2(a,b) > 0 });
  check(clause({ -f2(a,b) > 0, -f2(x, x) > 0 }), { -f2(a,b) > 0 });
  check(clause({ -f2(f(x),x) > 0, -f2(f(x), y) > 0 }), { -f2(f(x),x) > 0 });

  check(clause({ -f2(f(x) + a,x) > 0, -f2(f(x), y) > 0 }), { -f2(f(x) + a,x) > 0 });
}

TEST_FUN(selector_max_terms) {
  __ALLOW_UNUSED(
    SUGAR(Rat)
  )

  // auto cl = clause({
  //     x4 + -3300 + -40 * x3 > 0 | -20 X0 + -x4 + 4820 >= 0 | X0 + 2 x3 > 0 | X0 + 2 x3 > 0 | -X0 > 0 | -20 X0 + -x4 + 4820 >= 0 | X0 + -1 X0 >= 0
  //     });

  using namespace LiteralComparators;
  using SelectorMode = CompleteBestLiteralSelector<CompositeN
    < ColoredFirst
    , NegativeEquality
    , MaximalSize
    , Negative
    , LexComparator
    >>;

  auto state = testAlascaState(
      Options::UnificationWithAbstraction::ALASCA_MAIN,
      Lib::make_shared(InequalityNormalizer()),
      nullptr,
     /*uwaFixdPointIteration=*/ false,
     LiteralSelectors::selectorMode<SelectorMode>());


  auto check = [&](auto lit, auto expectedMax_) {
    auto expectedMax = expectedMax_.map([](auto x) { return TermList(x); }).collectStack().sorted();

    auto max = state->selector.maxAtomsNotLess(InequalityNormalizer::normalize(lit).template asItp<RatTraits>()->term())
      .map([](auto x) { return x.atom(); })
      .collectStack()
      .sorted();
    ASS_EQ(max, expectedMax);
  };

  // auto max = state->selector.maxAtomsNotLess(InequalityNormalizer::normalize(-20 * x + -a + 4820 >= 0).asItp<RatTraits>()->term())
  //   .collectStack()
  //   .sorted();
  // ASS_EQ(max, iterItems(x, a).collectStack().sorted())

  check(-20 * x + -a + 4820 >= 0, iterItems(x, a));

  // auto sel = state->selected(cl)
  //   .map([](auto& s) { return s.litIdx(); })
  //   .collectStack();
  //
  // ASS_EQ(sel, Stack<unsigned>{1})
}

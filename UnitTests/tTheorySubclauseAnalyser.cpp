
/*
 * File tInstantiation.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions.
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide.
 */

#include "Kernel/Signature.hpp"
#include "Lib/Environment.hpp"
#include "Shell/Analysis/TheorySubclauseAnalyser.hpp"
#include "Test/UnitTesting.hpp"

#define UNIT_ID TheorySubclauseAnalyser
UT_CREATE;

using namespace std;
using namespace Lib;
using namespace Kernel;
using namespace Shell;
using namespace Inferences;

#define $plus(...)                                                             \
  (AbsTerm::fun(plus, vvec<refw<AbsTerm>>{__VA_ARGS__})) // TODO
#define $times(...)                                                            \
  (AbsTerm::fun(times, vvec<refw<AbsTerm>>{__VA_ARGS__})) // TODO
#define $leq(...)                                                              \
  (create_abs_lit(true, sym_leq, vvec<refw<AbsTerm>>{__VA_ARGS__})) // TODO
#define f(...)                                                                 \
  (AbsTerm::fun(symbol_f, vvec<refw<AbsTerm>>{__VA_ARGS__})) // TODO
#define g(...)                                                                 \
  (AbsTerm::fun(symbol_g, vvec<refw<AbsTerm>>{__VA_ARGS__})) // TODO
#define x0 (AbsTerm::var(0))
#define x1 (AbsTerm::var(1))
#define x2 (AbsTerm::var(2))
#define x3 (AbsTerm::var(3))
#define x4 (AbsTerm::var(4))
#define x5 (AbsTerm::var(5))
#define x6 (AbsTerm::var(6))
#define x7 (AbsTerm::var(7))
#define x8 (AbsTerm::var(8))
#define x9 (AbsTerm::var(9))
#define x10 (AbsTerm::var(10))
#define x11 (AbsTerm::var(11))
#define x12 (AbsTerm::var(12))
#define x13 (AbsTerm::var(13))
#define x14 (AbsTerm::var(14))
#define x15 (AbsTerm::var(15))
#define x16 (AbsTerm::var(16))
#define x17 (AbsTerm::var(17))
#define x18 (AbsTerm::var(18))
#define x19 (AbsTerm::var(19))
#define x20 (AbsTerm::var(20))
#define x21 (AbsTerm::var(21))

#define SETUP                                                                  \
  unsigned symbol_f = env.signature->addFunction("f", 1);                      \
  unsigned symbol_g = env.signature->addFunction("g", 1);                      \
  unsigned sym_leq = env.signature->addInterpretedPredicate(                   \
      Interpretation::INT_LESS_EQUAL, "$leq");                                 \
  unsigned times = env.signature->addInterpretedFunction(                      \
      Interpretation::INT_MULTIPLY, "$times");                                 \
  unsigned plus = env.signature->addInterpretedFunction(                       \
      Interpretation::INT_PLUS, "$plus");

TEST_FUN(test_cmp_basic_term){

  SETUP

#define TO_TEST cmp2, cmp3, cmp4

#define DO_TEST(cmp_i)                                                         \
  {                                                                            \
    CALL(#cmp_i)                                                               \
    auto eq = [=](AbsTerm &l, AbsTerm &r) -> bool {                 \
      return cmp_i<AbsLiteral>{}($leq(l), $leq(r)) == CMP_EQUIV;                              \
    };                                                                         \
                                                                               \
    ASS(eq($plus(x1, $plus(x2, x3)), $plus(x1, $plus(x2, x3))))                \
    ASS(!eq($plus(x1, $times(x2, x3)), $times(x1, $plus(x2, x3))))             \
  }

  MAP(DO_TEST, TO_TEST)

#undef DO_TEST
#undef TO_TEST
}

TEST_FUN(test_cmp_rectified_term){
  SETUP

#define TO_TEST cmp3, cmp4

#define DO_TEST(cmp_i)                                                         \
  {                                                                            \
    CALL(#cmp_i)                                                               \
    auto eq = [=](AbsTerm &l, AbsTerm &r) -> bool {                 \
      return cmp_i<AbsLiteral>{}($leq(l), $leq(r)) == CMP_EQUIV;                              \
    };                                                                         \
                                                                               \
    ASS(eq($plus(x2, $times(x19, x7), x1), $plus(x5, $times(x3, x0), x2)))     \
  }

                                      MAP(DO_TEST, TO_TEST)

#undef DO_TEST
#undef TO_TEST
}

TEST_FUN(test_cmp_rectified_literal){SETUP

#define TO_TEST cmp3, cmp4

#define DO_TEST(cmp_i)                                                         \
  {                                                                            \
    CALL(#cmp_i)                                                               \
    auto eq = [=](const AbsLiteral &l, const AbsLiteral &r) -> bool {           \
      return cmp_i<AbsLiteral>{}(l, r) == CMP_EQUIV;                           \
    };                                                                         \
                                                                               \
    ASS(!eq($leq($plus(x1, x2), x2), $leq($plus(x1, x2), x3)))                 \
  }

  MAP(DO_TEST, TO_TEST)

#undef DO_TEST
#undef TO_TEST
}

TEST_FUN(test_cmp3) {
  SETUP

  auto eq = [=](AbsTerm &l, AbsTerm &r) -> bool {
      return cmp3<AbsLiteral>{}($leq(l), $leq(r)) == CMP_EQUIV;                              
  };

  ASS(eq($plus(x2, f(x19), x1), $plus(x5, f(f(x19)), x2)))
  ASS(eq($plus(x2, f(x19, f(x10)), x1), $plus(x5, f(f(x19)), x2)))
  ASS(!eq($plus(x1, f(x19, f(x10)), x1), $plus(x5, f(f(x19)), x2)))
  ASS(!eq($plus(x2, x8, x1), $plus(x5, f(f(x19)), x2)))
  ASS(eq(f(x1, x2, x2), g(x1, x2, x3)))
}

TEST_FUN(test_cmp4) {
  SETUP

  auto eq = [=](AbsTerm &l, AbsTerm &r) -> bool {
      return cmp4<AbsLiteral>{}($leq(l), $leq(r)) == CMP_EQUIV;                              
  };

  ASS(eq($plus(x2, f(x19), x1), $plus(x5, f(f(x19)), x2)))
  ASS(!eq($plus(x2, f(x19, f(x10)), x1), $plus(x5, f(f(x19)), x2)))
  ASS(!eq($plus(x1, f(x19, f(x10)), x1), $plus(x5, f(f(x19)), x2)))
  ASS(!eq($plus(x2, x8, x1), $plus(x5, f(f(x19)), x2)))
  ASS(!eq(f(x1, x2, x2), g(x1, x2, x3)))
}

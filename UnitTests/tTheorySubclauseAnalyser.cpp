
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
#include "Debug/PrintDebug.hpp"

#define UNIT_ID TheorySubclauseAnalyser
UT_CREATE;

using namespace std;
using namespace Lib;
using namespace Kernel;
using namespace Shell;
using namespace Inferences;

#define $leq(...)                                                              \
  (create_abs_lit(true, sym_leq, vvec<refw<AbsTerm>>{__VA_ARGS__})) // TODO
#define $neq(...)                                                             \
  (create_abs_lit(false, 0,  vvec<refw<AbsTerm>>{__VA_ARGS__})) // TODO
#define $equal(...)                                                             \
  (create_abs_lit(true, 0,  vvec<refw<AbsTerm>>{__VA_ARGS__})) // TODO

#define $sum(...)                                                             \
  (AbsTerm::fun(sum, vvec<refw<AbsTerm>>{__VA_ARGS__})) // TODO
#define $times(...)                                                            \
  (AbsTerm::fun(times, vvec<refw<AbsTerm>>{__VA_ARGS__})) // TODO
#define f(...)                                                                 \
  (AbsTerm::fun(symbol_f, vvec<refw<AbsTerm>>{__VA_ARGS__})) // TODO
#define g(...)                                                                 \
  (AbsTerm::fun(symbol_g, vvec<refw<AbsTerm>>{__VA_ARGS__}))

#define n(i) (AbsTerm::fun(env.signature->addIntegerConstant(0), vvec<refw<AbsTerm>>{}))

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

#define ALLOW_UNUSED(...) \
  _Pragma("GCC diagnostic push") \
  _Pragma("GCC diagnostic ignored \"-Wunused\"") \
  __VA_ARGS__ \
  _Pragma("GCC diagnostic pop")

#define SETUP                                                                  \
  ALLOW_UNUSED( \
  unsigned symbol_f = env.signature->addFunction("f", 1);                      \
  unsigned symbol_g = env.signature->addFunction("g", 1);                      \
  unsigned sym_leq = env.signature->addInterpretedPredicate(                   \
      Interpretation::INT_LESS_EQUAL, "$leq");                                 \
  unsigned times = env.signature->addInterpretedFunction(                      \
      Interpretation::INT_MULTIPLY, "$times");                                 \
  unsigned sum = env.signature->addInterpretedFunction(                       \
      Interpretation::INT_PLUS, "$sum");\
  )

TEST_FUN(test_cmp_basic_term){

    SETUP

#define TO_TEST 2, 3, 4

#define DO_TEST(i)                                                         \
  {                                                                            \
    CALL(#i)                                                               \
    auto eq = [=](AbsTerm &l, AbsTerm &r) -> bool {                            \
      return LitEquiv##i::compare($leq(l), $leq(r)) == CMP_EQUIV;               \
    };                                                                         \
                                                                               \
    ASS(eq($sum(x1, $sum(x2, x3)), $sum(x1, $sum(x2, x3))))                \
    ASS(!eq($sum(x1, $times(x2, x3)), $times(x1, $sum(x2, x3))))             \
  }

        MAP(DO_TEST, TO_TEST)

#undef DO_TEST
#undef TO_TEST
}

TEST_FUN(test_compare_rectified_term){SETUP

#define TO_TEST 3, 4

#define DO_TEST(i)                                                         \
  {                                                                            \
    CALL(#i)                                                               \
    auto eq = [=](AbsTerm &l, AbsTerm &r) -> bool {                            \
      l.rectify();                                                             \
      r.rectify();                                                             \
      return LitEquiv##i::compare($leq(l), $leq(r)) == CMP_EQUIV;               \
    };                                                                         \
                                                                               \
    ASS(eq($sum(x2, $times(x19, x7), x1), $sum(x5, $times(x3, x0), x2)))     \
  }

                                      MAP(DO_TEST, TO_TEST)

#undef DO_TEST
#undef TO_TEST
}

TEST_FUN(test_compare_rectified_literal){SETUP

#define TO_TEST 3, 4

#define DO_TEST(i)                                                         \
  {                                                                            \
    CALL(#i)                                                               \
    auto eq = [=](const AbsLiteral &l, const AbsLiteral &r) -> bool {          \
      return LitEquiv##i::compare(l, r) == CMP_EQUIV;                           \
    };                                                                         \
                                                                               \
    ASS(!eq($leq($sum(x1, x2), x2), $leq($sum(x1, x2), x3)))                 \
  }

                                         MAP(DO_TEST, TO_TEST)

#undef DO_TEST
#undef TO_TEST
}

TEST_FUN(test_compare3) {
  SETUP

  auto eq = [=](AbsTerm &l, AbsTerm &r) -> bool {
    return LitEquiv3::compare($leq(l), $leq(r)) == CMP_EQUIV;
  };

  ASS(eq($sum(x2, f(x19), x1), $sum(x5, f(f(x19)), x2)))
  ASS(eq($sum(x2, f(x19, f(x10)), x1), $sum(x5, f(f(x19)), x2)))
  ASS(!eq($sum(x1, f(x19, f(x10)), x1), $sum(x5, f(f(x19)), x2)))
  ASS(!eq($sum(x2, x8, x1), $sum(x5, f(f(x19)), x2)))
  ASS(eq(f(x1, x2, x2), g(x1, x2, x3)))
}

TEST_FUN(test_compare4) {
  SETUP

  auto eqLit = [=](AbsLiteral const &l, AbsLiteral const &r) -> bool {
    return LitEquiv4::compare(l, r) == CMP_EQUIV;
  };

  auto eq = [=](AbsTerm &l, AbsTerm &r) -> bool {
    return LitEquiv4::compare($leq(l), $leq(r)) == CMP_EQUIV;
  };

  ASS(eq($sum(x2, f(x19), x1), $sum(x5, f(f(x19)), x2)))
  ASS(!eq($sum(x2, f(x19, f(x10)), x1), $sum(x5, f(f(x19)), x2)))
  ASS(!eq($sum(x1, f(x19, f(x10)), x1), $sum(x5, f(f(x19)), x2)))
  ASS(!eq($sum(x2, x8, x1), $sum(x5, f(f(x19)), x2)))
  ASS(!eq(f(x1, x2, x2), g(x1, x2, x3)))
  ASS( eqLit( $neq(n(10), f(x7,g(x0, x7, x2))), $neq(n(-1), f(x2, x1, x3))))
}

TEST_FUN(test_normalize) {
  SETUP
  auto check_norm = [=](AbsLiteral& l, AbsLiteral& r) {
    normalize_absliteral(l);
    ASS(equal_absliteral(l, r));
  };
  check_norm($equal($sum(f(x0), n(0)), f(x0, x1)), $equal($sum(n(10), f(x0)), f(x0, x1)));
}

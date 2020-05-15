
/*
 * File tInterpretedFunctions.cpp.
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

#include "Forwards.hpp"
#include "Lib/Environment.hpp"

#include "Indexing/TermSharing.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Sorts.hpp"

#include "Kernel/InterpretedLiteralEvaluator.hpp"

#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"

#define UNIT_ID InterpretedFunctions
UT_CREATE;

using namespace std;
using namespace Lib;
using namespace Kernel;
using namespace Shell;

#define TEST_FAIL exit(-1);
#define OUT cout
// #define TEST_FAIL OUT << "FAIL" << endl;

namespace __Dumper {
  template<class... As>
  struct Dumper {
    static void dump(As... as);
  };

  template<>
  struct Dumper<> {
    static void dump() { }
  };

  template<class A, class... As>
  struct Dumper<A, As...> {
    static void dump(A a, As... as) {
      OUT << a;
      Dumper<As...>::dump(as...);
    }
  };
}

template<class... As>
void dump_all(As... as) {
  __Dumper::Dumper<As...>::dump(as...);
}

template<class... As>
void check(bool b, const char* msg, As... vs) {
  if (!b) {
    // OUT << endl;
    // OUT << msg << ": ";
    // dump_all(vs...);
    // OUT << endl;
    TEST_FAIL
  }
}

#define __CHECK(op, is, expected, msg, test_case) \
  if (!(( is ) op ( expected ))) { \
    OUT << endl; \
    OUT << msg << endl; \
    OUT << "[   case   ] " << test_case << endl; \
    OUT << "[    is    ] " << #is << " = " << is << endl; \
    OUT << "[ expected ] " << #is << " " #op << " " << expected << endl; \
    OUT << endl; \
    TEST_FAIL \
  } \

#define CHECK_NE(...) \
  __CHECK(!=, __VA_ARGS__)

#define CHECK_EQ(...) \
  __CHECK(==, __VA_ARGS__)

void check_no_succ(Literal& orig) {

  auto eval = NewEvaluator();

  // bool constant;
  // Literal* result = NULL;
  // bool constantTrue;
  //
  // auto sideConditions = Stack<Literal*>();
  Literal* src = Literal::create(&orig, orig.polarity());
  // auto success = eval.evaluate(src,constant,result,constantTrue, sideConditions);
  auto res = eval.evaluate(src);
  auto nop = res.tag() == LitEvalResult::NonTrivial && res.nonTrivialValue() == src;

  CHECK_EQ(nop, true, "unexpectedly evaluation was successful", orig.toString());
}


void check_eval(Literal& orig, bool expected) {

  auto eval = NewEvaluator();

  // auto eval = InterpretedLiteralEvaluator();
  //
  // bool constant;
  // Literal* result = NULL;
  // bool constantTrue;

  auto sideConditions = Stack<Literal*>();
  Literal* src = Literal::create(&orig, orig.polarity());
  // auto success = eval.evaluate(src,constant,result,constantTrue, sideConditions);

  // CHECK_EQ(success, true, "evaluation failed", orig.toString());
  // CHECK_EQ(sideConditions.isEmpty(), true, "non-empty side condictions", orig.toString());
  // CHECK_NE(result, NULL, "result not set", orig.toString());
  // CHECK_EQ(constant, true, "result not evaluated to constant", orig.toString());
  // CHECK_EQ(constantTrue, expected, "result not evaluated to constant", orig.toString());

  auto result = eval.evaluate(src);
  // auto nop = result.tag() == LitEvalResult::NonTrivial && result.nonTrivialValue() == src;
  CHECK_EQ(result.tag(), LitEvalResult::Trivial, "non-trivial evaluation result", orig.toString())
  CHECK_EQ(result.trivialValue(), expected, "result not evaluated to constant", orig.toString())
}

bool operator==(const Literal& lhs, const Literal& rhs) {
  return Indexing::TermSharing::equals(&lhs, &rhs);
}

void check_eval(Literal& orig, const Literal& expected) {

  auto eval = NewEvaluator();

  auto sideConditions = Stack<Literal*>();
  Literal* src = Literal::create(&orig, orig.polarity());

  auto result = eval.evaluate(src);
  CHECK_EQ(result.tag(), LitEvalResult::NonTrivial, "trivial evaluation result", orig.toString())
  CHECK_EQ(*result.nonTrivialValue(), expected, "result not evaluated correctly", orig.toString())

  // auto eval = InterpretedLiteralEvaluator();
  //
  // bool constant;
  // Literal* result = nullptr;
  // bool constantTrue;
  //
  // auto sideConditions = Stack<Literal*>();
  // auto success = eval.evaluate(&orig,constant,result,constantTrue, sideConditions);
  //
  // CHECK_EQ(success, true, "evaluation failed", orig.toString());
  // CHECK_EQ(sideConditions.isEmpty(), true, "non-empty side condictions", orig.toString());
  // CHECK_NE(result, NULL, "result not set", orig.toString());
  // CHECK_EQ(*result, expected, "unexpected evaluation result", orig.toString());

}

/** Tests for evalutions that should only be successful for reals/rationals and not for integers. */
#define FRACTIONAL_TEST(name, formula, expected) \
    TEST_FUN(name ## _ ## REAL) { \
      THEORY_SYNTAX_SUGAR(REAL); \
      check_eval(( formula ), ( expected )); \
    }\
    TEST_FUN(name ## _ ## RAT) { \
      THEORY_SYNTAX_SUGAR(RAT); \
      check_eval(( formula ), ( expected )); \
    } \

#define ALL_NUMBERS_TEST(name, formula, expected) \
    TEST_FUN(name ## _ ## INT) { \
      THEORY_SYNTAX_SUGAR(INT); \
      check_eval(( formula ), ( expected )); \
    } \
    TEST_FUN(name ## _ ## REAL) { \
      THEORY_SYNTAX_SUGAR(REAL); \
      check_eval(( formula ), ( expected )); \
    } \
    TEST_FUN(name ## _ ## RAT) { \
      THEORY_SYNTAX_SUGAR(RAT); \
      check_eval(( formula ), ( expected )); \
    } \

ALL_NUMBERS_TEST(partial_eval_add_1,
      eq(add(2, add(x, add(3, 7))), y),
      eq(add(12, x), y)
  )

ALL_NUMBERS_TEST(partial_eval_add_2,
      eq(add(2, add(add(8, x), add(3, 7))), y),
      eq(add(20, x), y)
)

ALL_NUMBERS_TEST(partial_eval_add_3,
      eq(add(2, add(add(minus(8), x), add(3, 7))), y),
      eq(add(4, x), y)
    )

ALL_NUMBERS_TEST(partial_eval_add_4,
      eq(minus(add(2, add(add(8, x), add(3, 7)))), y),
      eq(add(-20, minus(x)), y)
    )

ALL_NUMBERS_TEST(partial_eval_add_5,
    /* -21 + 7 * (3 + x) = y */
      eq(x, add(-21, mul(7, add(3,y)))),
      eq(x, mul(7,y))
    )

ALL_NUMBERS_TEST(partial_eval_add_6,
      eq(mul(7,x), add(-21, mul(7, add(3,x)))),
      true
    )

ALL_NUMBERS_TEST(simpl_times_zero_0
    , eq(a, mul(0, y))
    , eq(a, 0)
    );


ALL_NUMBERS_TEST(simpl_times_zero_1
    , eq(x, mul(0, y))
    , eq(x, 0)
    );

ALL_NUMBERS_TEST(simpl_times_zero_2
    , eq(3, add(mul(0, x), 4))
    , false
    );

FRACTIONAL_TEST(literal_to_const_1,
      eq(mul(frac(5,2), 2), 5),
      true 
      )

FRACTIONAL_TEST(literal_to_const_2,
      eq(mul(frac(5,2), 2), 6),
      false 
    )

FRACTIONAL_TEST(literal_to_const_3,
      lt(mul(3,2),5),
      false
    )

  // Interpret 3*2 < 5
FRACTIONAL_TEST(literal_to_const_4,
      neg(lt(mul(3,2),5)),
      true
    )

ALL_NUMBERS_TEST(literal_to_const_5,
      gt(mul(3,2),5),
      true
    )

ALL_NUMBERS_TEST(literal_to_const_6,
      gt(mul(3,2),13),
      false
    )

ALL_NUMBERS_TEST(literal_to_const_7,
      lt(0, 0),
      false
    );  

ALL_NUMBERS_TEST(literal_to_const_8,
      neg(lt(0, 0)),
      true
    )

ALL_NUMBERS_TEST(literal_to_const_9,
      gt(mul(3,a),mul(3, a)),
      false
    )

ALL_NUMBERS_TEST(literal_to_const_10,
      gt(add(mul(3,a), x),add(mul(3, a), x)),
      false
    )

ALL_NUMBERS_TEST(literal_to_const_11,
      gt(add(x, mul(3,a)),add(mul(3, a), x)),
      false
    )

// Interpret x = -x
ALL_NUMBERS_TEST(minus_x_eq_x,
      eq(x, minus(x)),
      eq(x, 0)
    )

ALL_NUMBERS_TEST(minus_x_neq_x,
      neq(x, minus(x)),
      neq(x, 0)
    )

#ifdef NORMALIZE_LESS //TODO
TEST_FUN(normalize_less_1) {
  THEORY_SYNTAX_SUGAR(INT)
  check_eval(
      /* 5 < 2 * x */
      lt(5, mul(2,x)),
      /* 0 < 2 * x - 5 */
      lt(0, add(-5, mul(2,x)))
    );
}

TEST_FUN(normalize_less_2) {
  THEORY_SYNTAX_SUGAR(INT)
  check_eval(
      /* 5 < a * x */
      lt(5, mul(a,x)),
      /* 0 < a * x - 5 */
      lt(0, add(-5, mul(a,x)))
    );
}

TEST_FUN(normalize_less_3) {
  THEORY_SYNTAX_SUGAR(INT)
  check_eval(
      /* b < a * x */
      lt(b, mul(a,x)),
     /* 0 < a * x - b */
      lt(0, add(mul(a,x), minus(b)))
    );

}

TEST_FUN(normalize_less_4) {
  THEORY_SYNTAX_SUGAR(INT)
  check_eval(
      /* b < a */
      lt(b, a),
      /* 0 < a - b */
      lt(0, add(a, minus(b)))
    );
}


TEST_FUN(normalize_less_5) {
  THEORY_SYNTAX_SUGAR(INT)
  check_eval(
      /* b < a */
      lt(x,y),
      /* 0 < a - b */
      lt(0, add(y, minus(x)))
    );
}

TEST_FUN(normalize_less_equal_1) {
  THEORY_SYNTAX_SUGAR(INT)
  check_eval(
      /* ~(x < 5) */
      neg(lt(x, 5)),
      /* 0 <  x - 4 */
      lt(0, add(-4, x))
    );
}

TEST_FUN(normalize_less_equal_2) {
  THEORY_SYNTAX_SUGAR(INT)
    /* 0 <= x + 1*/
  check_eval(
      neg(lt(x, a)),
      /* !(x < a) 
       * <-> a <= x 
       * <-> a - 1 < x 
       * <-> 0 < x + 1 - a
       */
      lt(0, add(add(1, x), minus(a)))
      );
}

TEST_FUN(test_normalize_stable) {
  THEORY_SYNTAX_SUGAR(INT)
    /* 0 <= x + 1*/
  // check_eval(
  //     leq(0, add(x, 1)),
  //     leq(0, add(x, 1))
      // );
  check_no_succ(
      lt(0, add(1, x))
      );
}
#endif // NORMALIZE_LESS // TODO

ALL_NUMBERS_TEST(misc_1,
      eq(mul(2, a), add(x, x)),
      eq(a, x)
      )

// x = -(-x)
ALL_NUMBERS_TEST(eval_double_minus_1_1, 
      eq(x, minus(minus(x))),
      true)

ALL_NUMBERS_TEST(eval_double_minus_1_2, 
      neg(eq(x, minus(minus(x)))),
      false)

// x < -(-x)
ALL_NUMBERS_TEST(eval_double_minus_2_1, 
      lt(x, minus(minus(x))),
      false)
ALL_NUMBERS_TEST(eval_double_minus_2_2, 
      neg(lt(x, minus(minus(x)))),
      true)

ALL_NUMBERS_TEST(eval_inverse_1 
    , eq(1, add(x, minus(x)))
    , false
    )

// a = -(-x)
ALL_NUMBERS_TEST(eval_double_minus_3,
      eq(a, minus(minus(x))),
      eq(a, x))


// 4 = -(-x + 4)
// ==> 4 = x + (-4)
ALL_NUMBERS_TEST(eval_double_minus_4,
      eq(4, minus(add(minus(x), 4))),
      eq(4, add(-4, x)) )

ALL_NUMBERS_TEST(eval_remove_identity_1,
      lt(0, add(0, minus(x))),
      lt(0, minus(x))
      )

ALL_NUMBERS_TEST(eval_remove_identity_2,
      eq(0, f(add(0, mul(x, mul(1, y))))),
      eq(0, f(mul(x,y)))
      )

ALL_NUMBERS_TEST(polynomial__normalize_uminus_1,
      p(mul(7, minus(f(x)))),
      p(mul(-7, f(x)))
      )

ALL_NUMBERS_TEST(polynomial__normalize_uminus_2,
      p(mul(minus(f(x)), 7)),
      p(mul(-7, f(x)))
      )

ALL_NUMBERS_TEST(polynomial__merge_consts_1,
      p(add(mul(6, x), mul(5, x))),
      p(mul(11, x))
      )

ALL_NUMBERS_TEST(polynomial__merge_consts_2,
      p(add(add(mul(6, x), mul(y, 3)), mul(5, x))),
      p(add(mul(11, x), mul(3,y)))
      )

ALL_NUMBERS_TEST(polynomial__merge_consts_3,
      p(add(add(mul(6, a), mul(y, 3)), mul(5, a))),
      p(add(mul(3, y), mul(11, a)))
      )

ALL_NUMBERS_TEST(polynomial__push_unary_minus,
      p(minus(mul(a, 7))),
      p(mul(-7, a))
      )

ALL_NUMBERS_TEST(polynomial__sorting,
      p(mul(mul(7, x), a)),
      p(mul(7, mul(x, a)))
      )

// TODO: cases x = k * x <-> k = 1 | x = 0 
// TODO: cases x = k + x <-> k = 0 
// TODO: cases x + x = k <->  = k/2


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
#include "Kernel/PolynomialNormalizer.hpp"

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

// TODO inline these macros
#define add(a,b) (a + b)
#define mul(a,b) (a * b)
#define minus(a) -(a)
#define lt(a,b) (a < b)
#define gt(a,b) (a > b)
#define leq(a,b) (a <= b)
#define geq(a,b) (a >= b)
#define neg(a)   ~(a)
#define eq(a,b)  (a == b)
#define neq(a,b) (a != b)

#define __CHECK(op, is, expected, msg, test_case) \
  if (!(( is ) op ( expected ))) { \
    OUT << endl; \
    OUT << msg << endl; \
    OUT << "[   case   ] " << test_case << endl; \
    OUT << "[    is    ] " << #is << " =  " << is << endl; \
    OUT << "[ expected ] " << #is << " " #op << " " << expected << endl; \
    OUT << endl; \
    TEST_FAIL \
  } \

#define CHECK_NE(...) __CHECK(!=, __VA_ARGS__) 
#define CHECK_EQ(...) __CHECK(==, __VA_ARGS__)

int testTermOrdering(TermList lhs, TermList rhs);
int testTermOrdering(const Term& lhs, const Term& rhs) {
  CALL("testTermOrdering")
  // DBG(lhs, " < ", rhs)
  auto run = [&]() {
    int l_fun = lhs.functor();
    int r_fun = rhs.functor();

    int l_thry = theory->isInterpretedFunction(l_fun);
    int r_thry = theory->isInterpretedFunction(r_fun);
    int cmp_thry = l_thry - r_thry;

    if (cmp_thry != 0) return cmp_thry;
    if (l_thry) {
      ASS(r_thry)

      int l_inter = theory->interpretFunction(l_fun);
      int r_inter = theory->interpretFunction(r_fun);
      int cmp_inter = l_inter - r_inter;

      if (cmp_inter != 0) return cmp_inter;

    } else {
      ASS(!l_thry && !r_thry)

#     define TRY_NUM(IntegerConstantType) \
        { \
          IntegerConstantType l; \
          IntegerConstantType r; \
          bool li = theory->tryInterpretConstant(&lhs, l); \
          bool ri = theory->tryInterpretConstant(&rhs, r); \
          int i = li - ri; \
          if (i != 0) return i; \
          if (li && l - r != IntegerConstantType(0)) {\
            return l - r > IntegerConstantType(0) ? 1 : -1;  \
          }\
        } \

      TRY_NUM(IntegerConstantType)
      TRY_NUM(RealConstantType)
      TRY_NUM(RationalConstantType)
   
      const vstring& lname = env.signature->getFunction(l_fun)->name();
      const vstring& rname = env.signature->getFunction(r_fun)->name();
      if (l_fun == r_fun) {

      } else if (lname < rname) {
        return -1;
      } else {
        return 1;
      }

      // if (cmp_fun != 0) return cmp_fun;
   }

    ASS(lhs.arity() == rhs.arity())
    for (int i = 0; i < lhs.arity(); i++) {
      auto cmp = testTermOrdering(lhs[i], rhs[i]);
      if (cmp != 0) {
        return cmp;
      }
    }
    return 0;
  };
  auto out = run();
  // DBG("=> ", out);
  return out;
}

int testTermOrdering(TermList lhs, TermList rhs) {
  CALL("testTermOrdering(TermList)")
  // DBG(lhs, " < ", rhs)
  auto run = [&](){

  auto l_trm = lhs.isTerm();
  auto r_trm = rhs.isTerm();
  auto cmp_trm = int(r_trm) - int(l_trm);
  if (cmp_trm != 0) return cmp_trm;

  if (l_trm) {
    ASS(r_trm);
    return testTermOrdering(*lhs.term(), *rhs.term());
  } else {
    ASS(lhs.isVar() && rhs.isVar());
    return int(lhs.var()) - int(rhs.var());
  }

  };
  auto out = run();
  // DBG("==> ", out);
  return out;

}

struct TestOrdering {
  bool operator()(const TermList& lhs, const TermList& rhs) const noexcept {
    // DBG("comparing: ", lhs, " < ", rhs)
    return testTermOrdering(lhs, rhs) < 0;
  }
};

#define NORMALIZER PolynomialNormalizer<PolynomialNormalizerConfig::Normalization<TestOrdering>>()

void check_no_succ(Literal& orig) {

  auto eval = NORMALIZER;

  Literal* src = Literal::create(&orig, orig.polarity());
  auto res = eval.evaluate(src);
  auto nop = res.template is<0>() && res.template unwrap<0>() == src;

  CHECK_EQ(nop, true, "unexpectedly evaluation was successful", orig.toString());
}


void check_eval(Lit orig_, bool expected) {
  Literal& orig = *orig_;

  auto eval = NORMALIZER;

  auto sideConditions = Stack<Literal*>();
  Literal* src = Literal::create(&orig, orig.polarity());

  auto result = eval.evaluate(src);
  CHECK_EQ(result.template is<1>(), true, "non-trivial evaluation result", orig.toString())
  CHECK_EQ(result.template unwrap<1>(), expected, "result not evaluated to constant", orig.toString())
}

bool operator==(const Literal& lhs, const Literal& rhs) {
  return Indexing::TermSharing::equals(&lhs, &rhs);
}

void check_eval(Lit orig_, Lit expected_) {
  Literal& orig = *orig_;
  const Literal& expected = *expected_;

  auto eval = NORMALIZER;

  auto sideConditions = Stack<Literal*>();
  Literal* src = Literal::create(&orig, orig.polarity());

  auto result = eval.evaluate(src);
  CHECK_EQ(result.template is<0>(), true, "trivial evaluation result", orig.toString())
  CHECK_EQ(*result.template unwrap<0>(), expected, "result not evaluated correctly", orig.toString())
}

#define ADDITIONAL_FUNCTIONS \
      _Pragma("GCC diagnostic push") \
      _Pragma("GCC diagnostic ignored \"-Wunused\"") \
        THEORY_SYNTAX_SUGAR_FUN(f, 1) \
        THEORY_SYNTAX_SUGAR_FUN(f2, 2) \
        THEORY_SYNTAX_SUGAR_PRED(p, 1) \
      _Pragma("GCC diagnostic pop") \

/** Tests for evalutions that should only be successful for reals/rationals and not for integers. */
#define FRACTIONAL_TEST(name, formula, expected) \
    TEST_FUN(name ## _ ## REAL) { \
      THEORY_SYNTAX_SUGAR(REAL); \
      ADDITIONAL_FUNCTIONS \
      check_eval(( formula ), ( expected )); \
    }\
    TEST_FUN(name ## _ ## RAT) { \
      THEORY_SYNTAX_SUGAR(RAT); \
      ADDITIONAL_FUNCTIONS \
      check_eval(( formula ), ( expected )); \
    } \

#define ALL_NUMBERS_TEST(name, formula, expected) \
    TEST_FUN(name ## _ ## INT) { \
      THEORY_SYNTAX_SUGAR(INT); \
      ADDITIONAL_FUNCTIONS \
      check_eval(( formula ), ( expected )); \
    } \
    TEST_FUN(name ## _ ## REAL) { \
      THEORY_SYNTAX_SUGAR(REAL); \
      ADDITIONAL_FUNCTIONS \
      check_eval(( formula ), ( expected )); \
    } \
    TEST_FUN(name ## _ ## RAT) { \
      THEORY_SYNTAX_SUGAR(RAT); \
      ADDITIONAL_FUNCTIONS \
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

FRACTIONAL_TEST(literal_to_const_0,
      num(0) == 31,
      false 
      )

FRACTIONAL_TEST(literal_to_const_1,
      eq(mul(frac(5,2), 2), 5),
      true 
      )

FRACTIONAL_TEST(literal_to_const_2,
      eq(mul(frac(5,2), 2), 6),
      false 
    )

FRACTIONAL_TEST(literal_to_const_3,
      (num(3) * num(2) < 5),
      false
    )

  // Interpret 3*2 < 5
FRACTIONAL_TEST(literal_to_const_4,
      ~(num(3) * 2 < 5),
      true
    )

ALL_NUMBERS_TEST(literal_to_const_5,
      (num(3) * 2) > 5,
      true
    )

ALL_NUMBERS_TEST(literal_to_const_6,
      ((num(3) * 2) > 13),
      false
    )

ALL_NUMBERS_TEST(literal_to_const_7,
      num(0) < 0,
      false
    );  

ALL_NUMBERS_TEST(literal_to_const_8,
      ~(num(0) < 0),
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
      eq(8, x) )

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
      p(add(mul(3,y), mul(11, x)))
      )

ALL_NUMBERS_TEST(polynomial__merge_consts_3,
      p(add(add(mul(6, a), mul(y, 3)), mul(5, a))),
      p(add(mul(3, y), mul(11, a)))
      )

ALL_NUMBERS_TEST(polynomial__push_unary_minus,
      p(minus(mul(a, 7))),
      p(mul(-7, a))
      )

ALL_NUMBERS_TEST(polynomial__sorting_1,
      p(mul(mul(7, x), a)),
      p(mul(7, mul(a, x)))
      )

ALL_NUMBERS_TEST(polynomial__sorting_2,
      p(mul(mul(7, mul(y, x)), a)),
      p(mul(7, mul(a, mul(x,y))))
      )

ALL_NUMBERS_TEST(polynomial__sorting_3,
      p(mul(add(x,add(x, y)), add(x, add(a,x)))),
    /* (x + x +y) * (x + a + x) */
    /* ==> (2x + y) * (2x + a) */
    /* ==> (2x + y) * (2x + a) */
    /* ==> (4x^2 + 2xy) + (2ax + ay) */
    /* ==> 4x^2 + 2xy + 2ax + ay */
      // p(add(mul(4, mul(x,x)), add(mul(2, mul(x,y)), add(mul(2,mul(x,a)), mul(y,a)))))
      p(add(mul(a,y),
        add(mul(2,mul(a,x)), 
        add(mul(2, mul(x,y)),
            mul(4, mul(x,x)) 
            ))))
      )

ALL_NUMBERS_TEST(polynomial__sorting_4,
      p((x + 1) * (x + -1)),
      /* (x + 1) * (x - 1) */
      p(add(-1, (x * x)))
      )

ALL_NUMBERS_TEST(polynomial__sorting_5,
      p(add(add(b,a),c)),
      p(add(a,add(b,c)))
      )

ALL_NUMBERS_TEST(polynomial__sorting_6,
      p((b * a) * c),
      p(a * (b * c))
      )

ALL_NUMBERS_TEST(eval_test_cached_1,
      p(((b * a) * c) *  ((b * a) * c)),
      p(a * (a * (b * (b * (c * c)))))
      )

ALL_NUMBERS_TEST(eval_test_cached_2,
      (b * a) * c == f((b * a) * c),
      a * (b * c) == f(a * (b * c))
      )

ALL_NUMBERS_TEST(eval_bug_1,
      p(f2(a,b)),
      p(f2(a,b))
      )

ALL_NUMBERS_TEST(eval_bug_2,
      x * (y * z) == (x * y) *z,
      true
      )

ALL_NUMBERS_TEST(eval_bug_3,
      x + (y + z) != (x + y) + z,
      false
      )

ALL_NUMBERS_TEST(eval_cancellation_0,
    x + 1 == 2,
    x     == 1
    )

ALL_NUMBERS_TEST(eval_cancellation_1,
    x + (-1) == -2,
    x        == -1
    )

ALL_NUMBERS_TEST(eval_cancellation_2,
    x + y == a + y,
    x     == a
    )

ALL_NUMBERS_TEST(eval_cancellation_3,
    3 + x == 2 + a,
    1 + x ==     a
    )

ALL_NUMBERS_TEST(eval_cancellation_4,
    x + (b * 3) == a + (b * 2),
    b + x == a
    )

ALL_NUMBERS_TEST(eval_cancellation_5,
    x + (y * 3) == a + (y * 2),
    x + y == a
    )

ALL_NUMBERS_TEST(eval_cancellation_6,
    x + (y * 3) + z + b == a + (y * 2) + z + (b * 3),
    x +  y              == a               +  2 * b
    )

// ALL_NUMBERS_TEST(eval_cancellation_7_nop,
//         x  == x * -1,
//         x  == minus(x)
//     // x + y  == a + (b * -4) or x + y  == a + (b * -4)
//     // x + y + (b * 4)  == a or x + y  == a + (b * -4)
//     )

ALL_NUMBERS_TEST(eval_cancellation_8,
    a * y * 6 == a * y * 2,
    4 * a * x == 0
    )


ALL_NUMBERS_TEST(eval_cancellation_9,
    a * y * -1 == a * y * -2,
     -(a * x)  == 0 
    )

//       x + 3 = a + 2         ==> x + 1 = a
//       x + 3 * b = a + 2 * b ==> x + b = a


// lG93(X0,X1,X2) = $sum($product(13.0,X2),$sum($product(-10.0,X1),$product(X0,-20.0)))

// TODO: cases x = k * x <-> k = 1 | x = 0 
// TODO: cases x = k + x <-> k = 0 
// TODO: cases x + x = k <->  = k/

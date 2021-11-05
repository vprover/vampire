/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Forwards.hpp"
#include "Lib/Environment.hpp"

#include "Indexing/TermSharing.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/PolynomialNormalizer.hpp"
#include "Inferences/PolynomialEvaluation.hpp"
#include "Inferences/PushUnaryMinus.hpp"
#include "Inferences/Cancellation.hpp"
#include "Test/TestUtils.hpp"
#include "Kernel/KBO.hpp"

#include "Kernel/InterpretedLiteralEvaluator.hpp"

#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"

using namespace std;
using namespace Lib;
using namespace Test;
using namespace Kernel;
using namespace Shell;
using namespace Inferences;
using LitSimplResult = Inferences::SimplifyingGeneratingLiteralSimplification::Result;

/////////////////////////////////////////////// Helper functions ///////////////////////////////////////////////////////

struct EqualityCheck {
  template<class A>
  bool operator()(A lhs, A rhs) const
  { return equalityCheck(lhs, rhs); }
};

bool equalityCheck(Literal& l, Literal& r) 
{ return TestUtils::eqModAC(&l,&r); }

bool equalityCheck(bool l, bool r) 
{ return l == r; }

bool equalityCheck(LitSimplResult& l, LitSimplResult& r) 
{ 
  if (l.template is<0>() && r.template is<0>()) return equalityCheck(*l.template unwrap<0>(), *r.template unwrap<0>());
  if (l.template is<1>() && r.template is<1>()) return equalityCheck( l.template unwrap<1>(),  r.template unwrap<1>());
  
  return false;
}

bool equalityCheck(Option<LitSimplResult>& l, Option<LitSimplResult>& r) 
{ 
  if (l.isSome()) {
    return r.isSome() && equalityCheck(l.unwrap(),r.unwrap());
  } else {
    return !r.isSome();
  }
}


#define __CHECK(op, is, expected, msg, test_case)                                                             \
  if (!(op equalityCheck( is, expected))) {                                                                   \
    auto& out = cout;                                                                                         \
    out << endl;                                                                                              \
    out << msg << endl;                                                                                       \
    out << "[   case   ] " << pretty(test_case) << endl;                                                      \
    out << "[    is    ] " << #is << " =  " << pretty(is) << endl;                                            \
    out << "[ expected ] " << #expected << " " #op "=" << " " << pretty(expected) << endl;                    \
    out << endl;                                                                                              \
    exit(-1);                                                                                                 \
  }                                                                                                           \

#define CHECK_NE(...) __CHECK(! , __VA_ARGS__) 
#define CHECK_EQ(...) __CHECK(  , __VA_ARGS__)

struct TestOrdering {
  bool operator()(const TermList& lhs, const TermList& rhs) const noexcept 
  { ASSERTION_VIOLATION }
};

#define NORMALIZER PolynomialNormalizer<PolynomialNormalizerConfig::Normalization<TestOrdering>>()


struct Failure { };
static Failure evaluationFail;

Option<LitSimplResult> evaluate(Literal* lit) 
{
  auto ord = KBO::testKBO();
  Ordering::trySetGlobalOrdering(SmartPtr<Ordering>(&ord, true));

  using Opt = Option<LitSimplResult>;
  auto& cl = *clause({lit});

  auto simpl = [](Clause* cl) -> Clause* 
  {

    auto _simpl = [](Clause* cl) -> Clause* 
    {
      PolynomialEvaluation norm(*Ordering::tryGetGlobalOrdering());
      PushUnaryMinus uminus;
      Cancellation cancel(*Ordering::tryGetGlobalOrdering());
      if (cl == nullptr) {
        return cl;
      } else {
        return norm.asISE().simplify(cancel.asISE().simplify(uminus.simplify(cl)));
      }
    };


    auto cur = cl;
    auto old = cl;
    do {
      old = cur;
      cur = _simpl(cur);
    } while (cur != old);
    return cur;
  };

  auto clOut = simpl(&cl);
  if (clOut == nullptr) {
    return Opt(LitSimplResult::constant(true));
  } else if (clOut->size() == 0) {
    return Opt(LitSimplResult::constant(false));
  } else {
    ASS_EQ(clOut->size(), 1)
    auto out = (*clOut)[0];
    if (out == lit) {
      return Opt();
    } else {
      return Opt(LitSimplResult::literal(out));
    }
  }
}

void check_eval(Lit orig_, Failure) {
  Literal& orig = *orig_;

  Literal* src = Literal::create(&orig, orig.polarity());
  auto res = evaluate(src);
  // auto expected = LitSimplResult::literal(src);
  auto expected = Option<LitSimplResult>();
       
  CHECK_EQ(expected, res, "unexpectedly evaluation was successful", orig);
}

template<>
std::ostream& Pretty<LitSimplResult>::prettyPrint(std::ostream& out) const
{ return out << pretty(static_cast<LitSimplResult::super const&>(_self)); }



void check_eval(Lit orig_, bool expected) {
  Literal& orig = *orig_;


  auto sideConditions = Stack<Literal*>();
  Literal* src = Literal::create(&orig, orig.polarity());

  auto result = evaluate(src);
  CHECK_EQ(result.isSome(), true, "evaluation not successful", orig)
  CHECK_EQ(result.unwrap().template is<1>(), true, "non-trivial evaluation result", orig)
  CHECK_EQ(result.unwrap().template unwrap<1>(), expected, "result not evaluated to constant", orig)
}

void check_eval(Lit orig_, Lit expected_) {
  Literal& orig = *orig_;
  Literal& expected = *expected_;

  auto sideConditions = Stack<Literal*>();
  Literal* src = Literal::create(&orig, orig.polarity());

  auto result = evaluate(src);

  CHECK_EQ(result.isSome(), true, "evaluation not successful", orig)
  CHECK_EQ(result.unwrap().template is<0>(), true, "trivial evaluation result", orig)
  CHECK_EQ(*result.unwrap().template unwrap<0>(), expected, "result not evaluated correctly", orig)
}

#define ADDITIONAL_FUNCTIONS(Num)                                                                             \
      __ALLOW_UNUSED(                                                                                         \
        DECL_CONST(a , Num)                                                                                   \
        DECL_CONST(b , Num)                                                                                   \
        DECL_CONST(c , Num)                                                                                   \
        DECL_FUNC(f , {Num}    , Num)                                                                         \
        DECL_FUNC(f2, {Num,Num}, Num)                                                                         \
        DECL_PRED(p, {Num})                                                                                   \
        DECL_PRED(r, {Num,Num})                                                                               \
      )                                                                                                       \

#define NUM_TEST(NUM, name, formula, expected)                                                                \
    TEST_FUN(name ## _ ## NUM) {                                                                              \
      __ALLOW_UNUSED(                                                                                         \
        NUMBER_SUGAR(NUM);                                                                                    \
        DECL_DEFAULT_VARS                                                                                     \
      )                                                                                                       \
      ADDITIONAL_FUNCTIONS(NUM)                                                                               \
      check_eval(( formula ), ( expected ));                                                                  \
    }                                                                                                         \

/** Tests for evalutions that should only be successful for reals/rationals and not for integers. */
#define FRACTIONAL_TEST(name, formula, expected)                                                              \
  NUM_TEST(Rat , name, formula, expected)                                                                     \
  NUM_TEST(Real, name, formula, expected)                                                                     \

#define INT_TEST(name, formula, expected)                                                                     \
  NUM_TEST(Int , name, formula, expected)                                                                     \

#define ALL_NUMBERS_TEST(name, formula, expected)                                                             \
  NUM_TEST(Int , name, formula, expected)                                                                     \
  NUM_TEST(Rat , name, formula, expected)                                                                     \
  NUM_TEST(Real, name, formula, expected)                                                                     \

/////////////////////////////////////////////// Test cases ///////////////////////////////////////////////////////

ALL_NUMBERS_TEST(partial_eval_add_1,
      2 + (x + (3 + 7)) == y, /* <- term to evaluate/normalize */
      12 + x            == y  /* <- expected result */
  )

ALL_NUMBERS_TEST(partial_eval_add_2,
      ((2 + ((8 + x) + (3 + 7))) == y),
      ((20 + x) == y)
)

ALL_NUMBERS_TEST(partial_eval_add_3,
      ((2 + ((-(8) + x) + (3 + 7))) == y),
      ((4 + x) == y)
    )

ALL_NUMBERS_TEST(partial_eval_add_4,
      (-((2 + ((8 + x) + (3 + 7)))) == y),
      ((-20 + -(x)) == y)
    )

ALL_NUMBERS_TEST(simpl_times_zero_0
    , (a == (0 * y))
    , (a == 0)
    );

ALL_NUMBERS_TEST(simpl_times_zero_1
    , (x == (0 * y))
    , (x == 0)
    );

ALL_NUMBERS_TEST(simpl_times_zero_2
    , (3 == ((0 * x) + 4))
    , false
    );

FRACTIONAL_TEST(literal_to_const_0,
      num(0) == 31,
      false
      )

FRACTIONAL_TEST(literal_to_const_1,
      ((frac(5,2) * 2) == 5),
      true
      )

FRACTIONAL_TEST(literal_to_const_2,
      ((frac(5,2) * 2) == 6),
      false
    )

FRACTIONAL_TEST(literal_to_const_3,
      (num(3) * num(2) < 5),
      false
    )


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
      ((3 * a) > (3 * a)),
      false
    )

ALL_NUMBERS_TEST(literal_to_const_10,
      (((3 * a) + x) > ((3 * a) + x)),
      false
    )

ALL_NUMBERS_TEST(literal_to_const_11,
      ((x + (3 * a)) > ((3 * a) + x)),
      false
    )


ALL_NUMBERS_TEST(eval_double_minus_1_1,
      (x == -(-(x))),
      true)

ALL_NUMBERS_TEST(eval_double_minus_1_2,
      ~((x == -(-(x)))),
      false)


ALL_NUMBERS_TEST(eval_double_minus_2_1,
      (x < -(-(x))),
      false)
ALL_NUMBERS_TEST(eval_double_minus_2_2,
      ~((x < -(-(x)))),
      true)

ALL_NUMBERS_TEST(eval_inverse_1
    , (1 == (x + -(x)))
    , false
    )


ALL_NUMBERS_TEST(eval_double_minus_3,
      (a == -(-(x))),
      (a == x))




ALL_NUMBERS_TEST(eval_double_minus_4,
      (-4 == -((-(x) + 4))),
      (0 == x) )

ALL_NUMBERS_TEST(eval_remove_identity_1,
      (0 < (0 + -(x))),
      (0 < -(x))
      )

ALL_NUMBERS_TEST(eval_remove_identity_2,
      (0 == f((0 + (x * (1 * y))))),
      (0 == f((x * y)))
      )

ALL_NUMBERS_TEST(polynomial__normalize_uminus_1,
      p((7 * -(f(x)))),
      p((-7 * f(x)))
      )

ALL_NUMBERS_TEST(polynomial__normalize_uminus_2,
      p((-(f(x)) * 7)),
      p((-7 * f(x)))
      )

ALL_NUMBERS_TEST(polynomial__normalize_uminus_3,
      p(-(num(7))),
      p(-7)
      )

ALL_NUMBERS_TEST(polynomial__merge_consts_1,
      p(((6 * x) + (5 * x))),
      p((11 * x))
      )

ALL_NUMBERS_TEST(polynomial__merge_consts_2,
      p((((6 * x) + (y * 3)) + (5 * x))),
      p(((3 * y) + (11 * x)))
      )

ALL_NUMBERS_TEST(polynomial__merge_consts_3,
      p((((6 * a) + (y * 3)) + (5 * a))),
      p(((3 * y) + (11 * a)))
      )

ALL_NUMBERS_TEST(polynomial__push_unary_minus,
      p(-((a * 7))),
      p((-7 * a))
      )

FRACTIONAL_TEST(test_div_1,
      p((a * 6) / 7),
      p(a * frac(6,7))
      )

// ALL_NUMBERS_TEST(polynomial__sorting_1,
//       p(((7 * x) * a)),
//       p((7 * (a * x)))
//       )
//
// ALL_NUMBERS_TEST(polynomial__sorting_2,
//       p(((7 * (y * x)) * a)),
//       p((7 * (a * (x * y))))
//       )
//
// ALL_NUMBERS_TEST(polynomial__sorting_3,
//       p(((x + (x + y)) * (x + (a + x)))),
//       p(((a * y) + ((2 * (a * x)) + ((2 * (x * y)) + (4 * (x * x))))))
//       )
//
// ALL_NUMBERS_TEST(polynomial__sorting_4,
//       p((x + 1) * (x + -1)),
//       p((-1 + (x * x)))
//       )
//
// ALL_NUMBERS_TEST(polynomial__sorting_5,
//       p(((b + a) + c)),
//       p((a + (b + c)))
//       )
//
// ALL_NUMBERS_TEST(polynomial__sorting_6,
//       p((b * a) * c),
//       p(a * (b * c))
//       )

ALL_NUMBERS_TEST(eval_test_cached_1,
      p(((b * a) * c) * ((b * a) * c)),
      // p(a * (a * (b * (b * (c * c)))))
      evaluationFail
      )

ALL_NUMBERS_TEST(eval_test_cached_2,
      (b * a) * c == f((b * a) * c),
      evaluationFail
      )

ALL_NUMBERS_TEST(eval_bug_1,
      p(f2(a,b)),
      evaluationFail
      )

ALL_NUMBERS_TEST(eval_bug_2,
      x * (y * z) == (x * y) * z,
      true
      )

ALL_NUMBERS_TEST(eval_bug_3,
      x + (y + z) != (x + y) + z,
      false
      )

ALL_NUMBERS_TEST(eval_bug_4,
    p((a + 3) + 3),
    p(a + 6)
    )

ALL_NUMBERS_TEST(eval_bug_5,
    p((3 + a) + 3),
    p(a + 6)
    )

ALL_NUMBERS_TEST(eval_bug_7,
    p((b + (3 * a)) + (4 * a)),
    p(b + 7 * a)
    )

ALL_NUMBERS_TEST(eval_cancellation_add_0,
    x + 1 == 2,
    x == 1
    )

ALL_NUMBERS_TEST(eval_cancellation_add_1,
    x + (-1) == -2,
    x + 1 == 0
    )

ALL_NUMBERS_TEST(eval_cancellation_add_2,
    x + y == a + y,
    x == a
    )

ALL_NUMBERS_TEST(eval_cancellation_add_3,
    3 + x == 2 + a,
    1 + x == a
    )

ALL_NUMBERS_TEST(eval_cancellation_add_4,
    x + (b * 3) == a + (b * 2),
    b + x == a
    )

ALL_NUMBERS_TEST(eval_cancellation_add_5,
    x + (y * 3) == a + (y * 2),
    x + y == a
    )

ALL_NUMBERS_TEST(eval_cancellation_add_6,
    x + (y * 3) + z + b == a + (y * 2) + z + (b * 3),
    x + y == a + 2 * b
    )

ALL_NUMBERS_TEST(eval_cancellation_add_8,
    a * y * 6 == a * y * 2,
    4 * (a * y) == 0
    )

ALL_NUMBERS_TEST(eval_cancellation_add_9,
    a * y * -1 == a * y * -2,
    0 == a * y 
    )

ALL_NUMBERS_TEST(eval_cancellation_add_10,
    a <= a + 3,
    true
    )

ALL_NUMBERS_TEST(eval_cancellation_add_11,
    x + a < a,
    x < 0
    )

INT_TEST(eval_quotientE_1,
    r(quotientE(num(7), 2), remainderE(num(7), 2)),
    r(                  3,                     1)
    )
INT_TEST(eval_quotientE_2,
    r(quotientE(num(-7), 2), remainderE(num(-7), 2)),
    r(                  -4 ,                     1 )
    )
INT_TEST(eval_quotientE_3,
    r(quotientE(num(7), -2), remainderE(num(7), -2)),
    r(                  -3 ,                1 )
    )

INT_TEST(eval_quotientE_4,
    p(quotientE(x, 1)),
    p(x)
    )

INT_TEST(eval_quotientE_4_1,
    p(remainderE(x, 1)),
    p(0)
    )

INT_TEST(eval_quotientF_1,
    r(quotientF(num(7), 2), remainderF(num(7), 2)),
    r(                  3,                     1)
    )


INT_TEST(eval_quotientT_1,
    r(quotientT(num(7), 2), remainderT(num(7), 2)),
    r(                  3,                     1)
    )

FRACTIONAL_TEST(eval_quotient_1,
    p(7 / frac(7, 2)),
    p(2)
    )

FRACTIONAL_TEST(div_zero_0,
    r(7 / num(0), num(10) + 1),
    r(7 / num(0), 11)
    )

INT_TEST(div_zero_1,
    r(quotientE(num(7), 0), num(10) + 1),
    r(quotientE(num(7), 0),     11     )
    )

INT_TEST(div_zero_2,
    r(remainderE(num(7), 0), num(10) + 1),
    r(remainderE(num(7), 0),     11     )
    )

ALL_NUMBERS_TEST(eval_overflow_1,
    p(num(1661992960) + 1661992960),
    evaluationFail
    )

ALL_NUMBERS_TEST(eval_overflow_2,
    r(num(1661992960) + 1661992960, num(7) + 3),
    r(num(1661992960) + 1661992960, 10)
    )

ALL_NUMBERS_TEST(eval_overflow_3,
    r(num(1661992960) * 1661992960, num(7) + 3),
    r(num(1661992960) * 1661992960, 10)
    )

ALL_NUMBERS_TEST(eval_overflow_4,
    p(-1 * num(std::numeric_limits<int>::min())),
    // p(-num(std::numeric_limits<int>::min()))
    evaluationFail
    )

ALL_NUMBERS_TEST(eval_overflow_5,
    p(std::numeric_limits<int>::min() * num(std::numeric_limits<int>::min() + 1) * std::numeric_limits<int>::min()),
    evaluationFail
    )

FRACTIONAL_TEST(eval_overflow_6,
    // p($sum(0.0555556,-1260453006.0)),
    p(frac(5,90) + num(-1260453006)),
    evaluationFail
    )

FRACTIONAL_TEST(eval_overflow_7,
    // p($sum(0.0555556,-1260453006.0)),
    frac(5,90) < num(-1260453006),
    false
    )

ALL_NUMBERS_TEST(NUM_IS_NUM_01,
     ~isInt(num(3)),
     false
    )

ALL_NUMBERS_TEST(NUM_IS_NUM_02,
     isInt(num(3)),
     true
    )

FRACTIONAL_TEST(NUM_IS_NUM_03,
     isInt(frac(3,2)),
     false
    )

FRACTIONAL_TEST(NUM_IS_NUM_04,
     isInt(frac(4,2)),
     true
    )

FRACTIONAL_TEST(NUM_IS_NUM_05,
     ~isInt(frac(3,2)),
     true
    )

FRACTIONAL_TEST(NUM_IS_NUM_06,
     isRat(frac(3,2)),
     true
    )

FRACTIONAL_TEST(NUM_IS_NUM_07,
     isReal(frac(3,2)),
     true
    )

ALL_NUMBERS_TEST(NUM_IS_NUM_08,
     ~isReal(num(3)),
     false
    )

// FRACTIONAL_TEST(eval_div_1,
//     p(floor(frac(7,2))),
//     p(3)
//     )
//
// FRACTIONAL_TEST(eval_div_1,
//     p(ceil(frac(7,2))),
//     p(4)
//     )



// not yet implemented:
// ALL_NUMBERS_TEST(eval_cancellation_mul_0,
//     x == a * x,
//     1 == a
//     )
//
// ALL_NUMBERS_TEST(eval_cancellation_mul_1,
//     2 * x == a * x,
//     2 == a
//     )
//
// ALL_NUMBERS_TEST(eval_cancellation_mul_2,
//     b * 2 * x == a * x * b,
//     /* dividing by ( b * x ) */
//     2 == a
//     )
//
// ALL_NUMBERS_TEST(eval_cancellation_mul_3,
//     b * 2 * x + x == a * x * b, 
//     /* dividing by x */
//     2 * b + 1     == a * b
//     )



//       x + 3 = a + 2         ==> x + 1 = a
//       x + 3 * b = a + 2 * b ==> x + b = a


// lG93(X0,X1,X2) = $sum($product(13.0,X2),$sum($product(-10.0,X1),$product(X0,-20.0)))

// TODO: cases x = k * x <-> k = 1 | x = 0 
// TODO: cases x = k + x <-> k = 0 
// TODO: cases x + x = k <-> x = k/2
//       p((x + 1) * (x + -1)) ==> p((-1 + (x * x)))

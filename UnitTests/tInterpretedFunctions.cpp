
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

#define UNIT_ID interpFunc
UT_CREATE;

using namespace std;
using namespace Lib;
using namespace Kernel;
using namespace Shell;

#define TEST_FAIL exit(-1);
#define OUT cout
// #define TEST_FAIL OUT << "FAIL" << endl;

#define x  TermList::var(0)
#define y TermList::var(1)

class TermWrapper {
  TermList _term;
public:
  TermWrapper(int i);
  TermWrapper(TermList t) : _term(t) {}
  operator TermList() {return _term;}
};

TermWrapper _mul(TermWrapper lhs, TermWrapper rhs, Theory::Interpretation inter_mult) { 
  return TermList( 
      Term::create2(env.signature->addInterpretedFunction(inter_mult, "mul"),  
        lhs, 
        rhs)); 
} 
 
TermWrapper _uminus(TermWrapper lhs, Theory::Interpretation uminus) { 
  return TermList( 
      Term::create1(env.signature->addInterpretedFunction(uminus, "minus"),  
        lhs)); 
} 
 
TermWrapper _add(TermWrapper lhs, TermWrapper rhs, Theory::Interpretation add_inter) { 
  return TermList( 
      Term::create2(env.signature->addInterpretedFunction(add_inter, "$sum"),  
        lhs, 
        rhs)); 
} 

#define constant(name) \
  TermWrapper _constant_ ## name (unsigned sort) {  \
    unsigned f = env.signature->addFunction(#name,0);  \
    static bool set = false;  \
    if (!set) {  \
      env.signature->getFunction(f)->setType(OperatorType::getFunctionType({},sort));  \
      set = true;  \
    }  \
    return TermList(Term::createConstant(f));  \
  } 

constant(a)
constant(b)
 
TermWrapper _f(TermWrapper args, unsigned sort) { 
  unsigned f = env.signature->addFunction("f",1); 
  static bool set = false; 
  if (!set) { 
    env.signature->getFunction(f)->setType(OperatorType::getFunctionType({ sort }, sort)); 
    set = true; 
  } 
  return TermList(Term::create1(f, args)); 
} 
 
TermWrapper num(int i) { 
  return TermList(theory->representConstant(IntegerConstantType(i))); 
} 
 
TermWrapper var(int i) {  
  return TermList::var(i);  
} 
 
TermWrapper real(int i) { 
  return TermList(theory->representConstant(RealConstantType(RationalConstantType(i)))); 
} 

TermWrapper::TermWrapper(int i) : TermWrapper(num(i)) { }
 
TermWrapper real(int a, int b) { 
  return TermList(theory->representConstant(RealConstantType(RationalConstantType(a,b)))); 
} 
 
Literal& neg(Literal& l) { 
  return *Literal::create(&l, !l.polarity());
} 

#define RELATION(name, inter) \
  auto name = [](TermWrapper lhs, TermWrapper rhs) -> Literal&  {  \
    return *Literal::create2(env.signature->addInterpretedPredicate(inter, #name),  \
        true, lhs,rhs);  \
  }; \
 
 
Literal& _eq(TermWrapper lhs, TermWrapper rhs, unsigned s) { 
  return *Literal::createEquality(true, lhs, rhs, s); 
} 
 
Literal& _neq(TermWrapper lhs, TermWrapper rhs, unsigned s) { 
  return *Literal::createEquality(false, lhs, rhs, s); 
}

#define INT_FROM_INT(x) x
#define REAL_FROM_INT(x) real(x)
#define INT_FROM_FRAC 
#define REAL_FROM_FRAC auto frac = [](int a, int b) -> TermWrapper { return real(a,b); };
#define _ECHO(x) x
#define CAT(x,y) _ECHO(x ## y)

#define TERM_FUNCTIONS(sort)  \
  _Pragma("GCC diagnostic push") \
  _Pragma("GCC diagnostic ignored \"-Wunused\"") \
    auto eq = [](TermWrapper lhs, TermWrapper rhs) -> Literal&  { return _eq(lhs,rhs, _TO_SORT_ ## sort); };  \
    auto neq = [](TermWrapper lhs, TermWrapper rhs) -> Literal& {  return _neq(lhs,rhs,_TO_SORT_ ## sort); };  \
    auto a = []() -> TermWrapper { return _constant_a(_TO_SORT_ ## sort); }; \
    auto b = []() -> TermWrapper { return _constant_b(_TO_SORT_ ## sort); }; \
    auto mul = [](TermWrapper lhs, TermWrapper rhs) -> TermWrapper {  return _mul(lhs,rhs,Theory::Interpretation:: sort ## _MULTIPLY); }; \
    auto uminus = [](TermWrapper lhs) -> TermWrapper { return _uminus(lhs,  Theory::Interpretation::sort ## _UNARY_MINUS); }; \
    auto add = [](TermWrapper lhs, TermWrapper rhs) -> TermWrapper { return _add(lhs,rhs, Theory::Interpretation::sort ## _PLUS); }; \
    auto f = [](TermWrapper args) -> TermWrapper { return _f(args, _TO_SORT_ ## sort); }; \
    auto i = [](int k) -> TermWrapper { return sort ## _FROM_INT(k); }; \
    sort ## _FROM_FRAC \
    RELATION(gt, Theory::Interpretation::sort ## _GREATER)\
    RELATION(geq, Theory::Interpretation::sort ## _GREATER_EQUAL)\
    RELATION(lt, Theory::Interpretation::sort ## _LESS)\
    RELATION(leq, Theory::Interpretation::sort ## _LESS_EQUAL)\
  _Pragma("GCC diagnostic pop") \

#define _TO_SORT_INT Sorts::SRT_INTEGER
#define _TO_SORT_REAL Sorts::SRT_REAL
 
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

template<class A>
void check_eq(A l, A r, const char* msg, const Literal& input) {
  if (l != r) {
    // OUT << endl;
    // std::OUT << msg << ". input: " << input << "\t is: " << l << "\t expected: " << r;
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

  auto eval = InterpretedLiteralEvaluator();

  bool constant;
  Literal* result = NULL;
  bool constantTrue;

  auto sideConditions = Stack<Literal*>();
  Literal* src = Literal::create(&orig, orig.polarity());
  auto success = eval.evaluate(src,constant,result,constantTrue, sideConditions);

  CHECK_EQ(success, false, "unexpectedly evaluation was successful", orig.toString());
  // CHECK_EQ(result, NULL, "result was set", orig.toString());
  // CHECK_EQ(sideConditions.isEmpty(), true, "non-empty side condictions", orig.toString());
  // CHECK_EQ(constant, true, "result not evaluated to constant", orig.toString());
  // CHECK_EQ(constantTrue, expected, "result not evaluated to constant", orig.toString());
}


void check_eval(Literal& orig, bool expected) {

  auto eval = InterpretedLiteralEvaluator();

  bool constant;
  Literal* result = NULL;
  bool constantTrue;

  auto sideConditions = Stack<Literal*>();
  Literal* src = Literal::create(&orig, orig.polarity());
  auto success = eval.evaluate(src,constant,result,constantTrue, sideConditions);

  CHECK_EQ(success, true, "evaluation failed", orig.toString());
  CHECK_EQ(sideConditions.isEmpty(), true, "non-empty side condictions", orig.toString());
  CHECK_NE(result, NULL, "result not set", orig.toString());
  CHECK_EQ(constant, true, "result not evaluated to constant", orig.toString());
  CHECK_EQ(constantTrue, expected, "result not evaluated to constant", orig.toString());
}

bool operator==(const Literal& lhs, const Literal& rhs) {
  return Indexing::TermSharing::equals(&lhs, &rhs);
}

void check_eval(Literal& orig, const Literal& expected) {
  auto eval = InterpretedLiteralEvaluator();

  bool constant;
  Literal* result = nullptr;
  bool constantTrue;

  auto sideConditions = Stack<Literal*>();
  auto success = eval.evaluate(&orig,constant,result,constantTrue, sideConditions);

  CHECK_EQ(success, true, "evaluation failed", orig.toString());
  CHECK_EQ(sideConditions.isEmpty(), true, "non-empty side condictions", orig.toString());
  CHECK_NE(result, NULL, "result not set", orig.toString());
  CHECK_EQ(*result, expected, "unexpected evaluation result", orig.toString());
  // check(Indexing::TermSharing::equals(result, &expected), "unexpected evaluation", 
  //     orig.toString(), "\t->\t", result->toString(), "\tis not\t", expected.toString());

}

//TODO add rationals
/** Tests for evalutions that should only be successful for reals/rationals and not for integers. */
#define FRACTIONAL_TEST(name, formula, expected) \
  TEST_FUN(name ## _int) { \
    TERM_FUNCTIONS(INT); \
    check_no_succ(( formula )); \
  } \
  TEST_FUN(name ## _real) { \
    TERM_FUNCTIONS(REAL); \
    check_eval(( formula ), ( expected )); \
  } \

//TODO add rationals
#define ALL_NUMBERS_TEST(name, formula, expected) \
  TEST_FUN(name ## _int) { \
    TERM_FUNCTIONS(INT); \
    check_eval(( formula ), ( expected )); \
  } \
  TEST_FUN(name ## _real) { \
    TERM_FUNCTIONS(REAL); \
    check_eval(( formula ), ( expected )); \
  } \

FRACTIONAL_TEST(rebalance_var_1
    , eq(mul(i(2), x), i(5))
    , eq(frac(5,2), x)
    )

ALL_NUMBERS_TEST(rebalance_var_2
    , eq(add(i(2), x), i(4))
    , eq(i(2), x)
    );

  //TODO continue here
TEST_FUN(partial_eval_add_1) { 
  TERM_FUNCTIONS(INT)
  check_eval(
      eq(add(i(2), add(x, add(i(3), i(7)))), y),
      eq(add(i(12), x), y)
    );
}

TEST_FUN(partial_eval_add_2) { 
  TERM_FUNCTIONS(INT)
  check_eval(
      eq(add(i(2), add(add(i(8), x), add(i(3), i(7)))), y),
      eq(add(i(20), x), y)
    );
}

TEST_FUN(partial_eval_add_3) { 
  TERM_FUNCTIONS(INT)
  check_eval(
      eq(add(2, add(add(uminus(8), x), add(3, 7))), y),
      eq(add(4, x), y)
    );
}

TEST_FUN(partial_eval_add_4) { 
  TERM_FUNCTIONS(INT)
  check_eval(
      eq(uminus(add(2, add(add(8, x), add(3, 7)))), y),
      eq(add(-20, uminus(x)), y)
    );
}

#if 0 // NOT (YET) SUPPORTED

TEST_FUN(partial_eval_add_mul_1) { 
  TERM_FUNCTIONS(INT)
    /* -21 + 7 * (3 + x) = y */
  check_eval(
      eq(x, add(-21, mul(7, add(3,y)))),
      eq(x, mul(7,y))
    );
}

TEST_FUN(partial_eval_add_mul_2) { 
  TERM_FUNCTIONS(INT)
  check_eval(
      eq(mul(7,x), add(-21, mul(7, add(3,x)))),
      true
    );
}

#endif

TEST_FUN(rebalance_var_uninter_1) { 
  TERM_FUNCTIONS(REAL)
  check_eval(
      eq(add(real(2), x), a()),
      eq(add(real(-2), a()), x)
    );
}


TEST_FUN(rebalance_var_uninter_2) { 
  TERM_FUNCTIONS(INT)
  check_eval(
      eq(add(2, x), a()),
      eq(add(-2, a()), x)
    );
}

FRACTIONAL_TEST(rebalance_var_uninter_4
    , eq(mul(x, i(2)), a())
    , eq(x, mul(frac(1, 2), a()))
    )

FRACTIONAL_TEST(rebalance_var_uninter_5
    , eq(mul(x, i(2)), i(1))
    , eq(x, frac(1, 2))
    )

  //TODO 2*x = 4 * y ==> x = 2 * y for ints

TEST_FUN(rebalance_mul_zero_1) {
  TERM_FUNCTIONS(REAL)
  check_eval(
      eq(x, mul(i(0), y))
    , eq(x, i(0))
    );
}

TEST_FUN(rebalance_mul_zero_2) {
  TERM_FUNCTIONS(REAL)
  check_eval(
      eq(a(), mul(i(0), x))
    , eq(a(), i(0))
    );
}

TEST_FUN(rebalance_mul_zero_3) {
  TERM_FUNCTIONS(REAL)
  check_eval(
      eq(i(3), add(mul(i(0), x), i(4)))
    , false
    );
}


TEST_FUN(rebalance_multiple_vars) {
  TERM_FUNCTIONS(REAL)
  check_eval(
      eq(add(x, uminus(y)), f(y))
    , eq(x, add(y, f(y)))
    );
}


TEST_FUN(literal_to_const_1) {
  TERM_FUNCTIONS(REAL)
  // Interpret 2.5*2=5
  check_eval(
      eq(mul(real(5,2), real(2)), real(5)),
      true 
    );
}

TEST_FUN(literal_to_const_2) {
  TERM_FUNCTIONS(REAL)
  check_eval(
      eq(mul(real(5,2), real(2)), real(6)),
      false 
    );
}

TEST_FUN(literal_to_const_3) {
  TERM_FUNCTIONS(INT)

  // Interpret 3*2 < 5
  check_eval(
      lt(mul(3,2),5),
      false
    );

  // Interpret 3*2 < 5
  check_eval(
      neg(lt(mul(3,2),5)),
      true
    );

}

TEST_FUN(literal_to_const_4) {
  TERM_FUNCTIONS(REAL)

  // Interpret 3*2 > 5
  check_eval(
      gt(mul(real(3),real(2)),real(5)),
      true
    );

}

TEST_FUN(literal_to_const_5) {
  TERM_FUNCTIONS(REAL)
  // Interpret 3*2 > 13
  check_eval(
      gt(mul(real(3),real(2)),real(13)),
      false
    );
}

TEST_FUN(literal_to_const_6) {
  TERM_FUNCTIONS(INT)
  check_eval(
      lt(i(0), i(0)),
      false
    );  
  check_eval(
      neg(lt(i(0), i(0))),
      true
    );
}

#ifdef TEST_EVAL


TEST_FUN(literal_to_const_7) { 
  TERM_FUNCTIONS(REAL)
  // Interpret 13*a > 13*a
  check_eval(
      gt(add(mul(real(3),a()), x),add(mul(real(3), a()), x)),
      false
    );
}

TEST_FUN(literal_to_const_8) {
  TERM_FUNCTIONS(REAL)

  // Interpret 3*a > 13*a
  check_eval(
      gt(mul(real(3),a()),mul(real(13), a())),
      false
    );
}

TEST_FUN(literal_to_const_9) {
  TERM_FUNCTIONS(REAL)

  // Interpret 18*a > 13*a
  check_eval(
      gt(mul(real(18),a()),mul(real(13), a())),
      true
    );
}

// Interpret 5.0 = 2.0 * y(5.0)
TEST_FUN(rebalance_uninterpreted) {
  TERM_FUNCTIONS(REAL)

  check_eval(
      eq(real(5), mul(real(2),f(real(5)))),
      eq(f(real(5)), real(5,2))
    );

}

// Interpret x = -x
TEST_FUN(minus_x_eq_x) {
  TERM_FUNCTIONS(REAL)

  check_eval(
      eq(x, uminus(x)),
      eq(x, real(0))
    );
}

TEST_FUN(minus_x_neq_x) {
  TERM_FUNCTIONS(REAL)

  check_eval(
      neq(x, uminus(x)),
      neq(x, real(0))
    );

};

// Interpret k*x = 0
TEST_FUN(k_x_eq_0) {
  TERM_FUNCTIONS(REAL)

  check_eval(
      eq(mul(real(5),x), real(0)),
      eq(x, real(0))
    );

  check_eval(
      eq(mul(real(5),a()), real(0)),
      eq(a(), real(0))
    );

};

#endif

TEST_FUN(normalize_less_1) {
  TERM_FUNCTIONS(INT)
  check_eval(
      /* 5 < 2 * x */
      lt(5, mul(2,x)),
      /* 0 < 2 * x - 5 */
      lt(0, add(-5, mul(2,x)))
    );
}

TEST_FUN(normalize_less_2) {
  TERM_FUNCTIONS(INT)
  check_eval(
      /* 5 < a * x */
      lt(5, mul(a(),x)),
      /* 0 < a * x - 5 */
      lt(0, add(-5, mul(a(),x)))
    );
}

TEST_FUN(normalize_less_3) {
  TERM_FUNCTIONS(INT)
  check_eval(
      /* b < a * x */
      lt(b(), mul(a(),x)),
     /* 0 < a * x - b */
      lt(0, add(mul(a(),x), uminus(b())))
    );

}

TEST_FUN(normalize_less_4) {
  TERM_FUNCTIONS(INT)
  check_eval(
      /* b < a */
      lt(b(), a()),
      /* 0 < a - b */
      lt(0, add(a(), uminus(b())))
    );
}


TEST_FUN(normalize_less_5) {
  TERM_FUNCTIONS(INT)
  check_eval(
      /* b < a */
      lt(x,y),
      /* 0 < a - b */
      lt(0, add(y, uminus(x)))
    );
}

TEST_FUN(normalize_less_equal_1) {
  TERM_FUNCTIONS(INT)
  check_eval(
      /* ~(x < 5) */
      neg(lt(x, 5)),
      /* 0 <  x - 4 */
      lt(0, add(-4, x))
    );
}

TEST_FUN(normalize_less_equal_2) {
  TERM_FUNCTIONS(INT)
    /* 0 <= x + 1*/
  check_eval(
      neg(lt(x, a())),
      /* !(x < a) 
       * <-> a <= x 
       * <-> a - 1 < x 
       * <-> 0 < x + 1 - a
       */
      lt(0, add(add(1, x), uminus(a())))
      );
}

TEST_FUN(test_normalize_stable) {
  TERM_FUNCTIONS(INT)
    /* 0 <= x + 1*/
  // check_eval(
  //     leq(0, add(x, 1)),
  //     leq(0, add(x, 1))
      // );
  check_no_succ(
      lt(0, add(1, x))
      );
}

#ifdef TEST_EVAL
TEST_FUN(x_eq_kx_1) {
  TERM_FUNCTIONS(INT)
  check_eval(
      eq(x, mul(x, 3)),
      eq(0, x)
      );
}

TEST_FUN(x_eq_k_plus_x_1) {
  TERM_FUNCTIONS(INT)
  check_eval(
      eq(x, add(x, y)),
      eq(y, 0)
      );
}


TEST_FUN(x_eq_k_plus_x_2) {
  TERM_FUNCTIONS(INT)
  check_eval(
      eq(x, add(x, 1)),
      false
      );
}

TEST_FUN(k_eq_x_plus_x_1) {
  TERM_FUNCTIONS(INT)
  check_eval(
      eq(mul(2, a()), add(x, x)),
      eq(a(), x)
      );
}

// Interpret -x > x
TEST_FUN(x_gt_minus_x) {
  TERM_FUNCTIONS(REAL)

  check_eval(
      gt(x, uminus(x)),
      gt(x, real(0))
    );

  check_eval(
      gt(uminus(x), x),
      gt(real(0), x)
    );
};


#endif


// x = -(-x)
TEST_FUN(eval_double_minus_1) {
  TERM_FUNCTIONS(INT)

  check_eval(
      eq(x, uminus(uminus(x))),
      true);
  check_eval(
      neg(eq(x, uminus(uminus(x)))),
      false);
};


// x < -(-x)
TEST_FUN(eval_double_minus_2) {
  TERM_FUNCTIONS(INT)

  check_eval(
      lt(x, uminus(uminus(x))),
      false);
  check_eval(
      neg(lt(x, uminus(uminus(x)))),
      true);
};


// a = -(-x)
TEST_FUN(eval_double_minus_3) {
  TERM_FUNCTIONS(INT)

  check_eval(
      eq(a(), uminus(uminus(x))),
      eq(a(), x));
};


// 4 = -(-x + 4)
// ==> 4 = x + (-4)
TEST_FUN(eval_double_minus_4) {
  TERM_FUNCTIONS(INT)
  check_eval(
      eq(4, uminus(add(uminus(x), 4))),
      eq(8, x) );
};

TEST_FUN(eval_remove_identity_1) {
  TERM_FUNCTIONS(INT)
  check_eval(
      lt(0, add(0, uminus(x))),
      lt(0, uminus(x))
      );
};

TEST_FUN(eval_remove_identity_2) {
  TERM_FUNCTIONS(INT)
  check_eval(
      eq(0, f(add(0, uminus(mul(x, mul(1, y)))))),
      eq(0, f(uminus(mul(x,y))))
      );
};


// TODO: cases x = k * x <-> k = 1 | x = 0 
// TODO: cases x = k + x <-> k = 0 
// TODO: cases x + x = k <->  = k/2

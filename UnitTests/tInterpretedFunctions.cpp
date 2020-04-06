
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
#define OUT cerr
// #define TEST_FAIL OUT << "FAIL" << endl;

#define x  TermList::var(0)
#define x1 TermList::var(1)

TermList _mul(TermList lhs, TermList rhs, Theory::Interpretation inter_mult) { 
  return TermList( 
      Term::create2(env.signature->addInterpretedFunction(inter_mult, "mul"),  
        lhs, 
        rhs)); 
} 
 
TermList _uminus(TermList lhs, Theory::Interpretation uminus) { 
  return TermList( 
      Term::create1(env.signature->addInterpretedFunction(uminus, "minus"),  
        lhs)); 
} 
 
TermList _add(TermList lhs, TermList rhs, Theory::Interpretation add_inter) { 
  return TermList( 
      Term::create2(env.signature->addInterpretedFunction(add_inter, "$sum"),  
        lhs, 
        rhs)); 
} 

#define constant(name) \
  TermList _constant_ ## name (unsigned sort) {  \
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
 
TermList _f(TermList args, unsigned sort) { 
  unsigned f = env.signature->addFunction("f",1); 
  static bool set = false; 
  if (!set) { 
    env.signature->getFunction(f)->setType(OperatorType::getFunctionType({ sort }, sort)); 
    set = true; 
  } 
  return TermList(Term::create1(f, args)); 
} 
 
TermList num(int i) { 
  return TermList(theory->representConstant(IntegerConstantType(i))); 
} 
 
TermList var(int i) {  
  return TermList::var(i);  
} 
 
TermList real(int i) { 
  return TermList(theory->representConstant(RealConstantType(RationalConstantType(i)))); 
} 
 
TermList real(int a, int b) { 
  return TermList(theory->representConstant(RealConstantType(RationalConstantType(a,b)))); 
} 
 
Literal& neg(Literal& l) { 
  return *Literal::create(&l, false);
} 

#define RELATION(name, inter) \
  auto name = [](TermList lhs, TermList rhs) -> Literal&  {  \
    return *Literal::create2(env.signature->addInterpretedPredicate(inter, #name),  \
        true, lhs,rhs);  \
  }; \
 
 
Literal& _eq(TermList lhs, TermList rhs, unsigned s) { 
  return *Literal::createEquality(true, lhs, rhs, s); 
} 
 
Literal& _neq(TermList lhs, TermList rhs, unsigned s) { 
  return *Literal::createEquality(false, lhs, rhs, s); 
}


#define TERM_FUNCTIONS(sort)  \
  _Pragma("GCC diagnostic push") \
  _Pragma("GCC diagnostic ignored \"-Wunused\"") \
    auto eq = [](TermList lhs, TermList rhs) -> Literal&  { return _eq(lhs,rhs, _TO_SORT_ ## sort); };  \
    auto neq = [](TermList lhs, TermList rhs) -> Literal& {  return _neq(lhs,rhs,_TO_SORT_ ## sort); };  \
    auto a = []() -> TermList { return _constant_a(_TO_SORT_ ## sort); }; \
    auto b = []() -> TermList { return _constant_b(_TO_SORT_ ## sort); }; \
    auto mul = [](TermList lhs, TermList rhs) -> TermList {  return _mul(lhs,rhs,Theory::Interpretation:: sort ## _MULTIPLY); }; \
    auto uminus = [](TermList lhs) -> TermList { return _uminus(lhs,  Theory::Interpretation::sort ## _UNARY_MINUS); }; \
    auto add = [](TermList lhs, TermList rhs) -> TermList { return _add(lhs,rhs, Theory::Interpretation::sort ## _PLUS); }; \
    auto f = [](TermList args) -> TermList { return _f(args, _TO_SORT_ ## sort); }; \
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
  } \

#define CHECK_NE(...) \
  __CHECK(!=, __VA_ARGS__)

#define CHECK_EQ(...) \
  __CHECK(==, __VA_ARGS__)

void check_eval(Literal& orig, bool expected) {

  auto eval = InterpretedLiteralEvaluator();

  bool constant;
  Literal* result = NULL;
  bool constantTrue;

  auto sideConditions = Stack<Literal*>();
  auto success = eval.evaluate(&orig,constant,result,constantTrue, sideConditions);

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


// Interpret x*2=5
TEST_FUN(rebalance_var_1) { 
  TERM_FUNCTIONS(REAL)

  check_eval(
      eq(mul(real(2), x), real(5)),
      eq(real(5,2), x)
    );
}

TEST_FUN(rebalance_var_2) { 
  TERM_FUNCTIONS(REAL)

  check_eval(
      eq(add(real(2), x), real(4)),
      eq(real(2), x)
    );
}

TEST_FUN(rebalance_var_3) { 
  TERM_FUNCTIONS(REAL)

  check_eval(
      eq(add(real(2), x), a()),
      eq(add(a(), real(-2)), x)
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
  TERM_FUNCTIONS(REAL)

  // Interpret 3*2 > 5
  check_eval(
      gt(mul(real(3),real(2)),real(5)),
      true
    );

}

TEST_FUN(literal_to_const_4) {
  TERM_FUNCTIONS(REAL)
  // Interpret 3*2 > 13
  check_eval(
      gt(mul(real(3),real(2)),real(13)),
      false
    );
}

TEST_FUN(literal_to_const_5) { 
  TERM_FUNCTIONS(REAL)
  // Interpret 13*a > 13*a
  check_eval(
      gt(add(mul(real(3),a()), x),add(mul(real(3), a()), x)),
      false
    );
}

TEST_FUN(literal_to_const_6) {
  TERM_FUNCTIONS(REAL)

  // Interpret 3*a > 13*a
  check_eval(
      gt(mul(real(3),a()),mul(real(13), a())),
      false
    );
}

TEST_FUN(literal_to_const_7) {
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

TEST_FUN(normalize_less_1) {
  TERM_FUNCTIONS(INT)
  check_eval(
      /* 5 < 2 * x */
      lt(num(5), mul(num(2),x)),
      /* 0 < 2 * x - 5 */
      lt(num(0), add(mul(num(2),x), num(-5)))
    );
}

TEST_FUN(normalize_less_2) {
  TERM_FUNCTIONS(INT)
  check_eval(
      /* 5 < a * x */
      lt(num(5), mul(a(),x)),
      /* 0 < a * x - 5 */
      lt(num(0), add(mul(a(),x), num(-5)))
    );
}

TEST_FUN(normalize_less_3) {
  TERM_FUNCTIONS(INT)
  check_eval(
      /* b < a * x */
      lt(b(), mul(a(),x)),
     /* 0 < a * x - b */
      lt(num(0), add(mul(a(),x), uminus(b())))
    );

}

TEST_FUN(normalize_less_4) {
  TERM_FUNCTIONS(INT)
  check_eval(
      /* b < a */
      lt(b(), mul(a(),x)),
      /* 0 < a - b */
      lt(num(0), add(a(), uminus(b())))
    );
}


TEST_FUN(normalize_less_5) {
  TERM_FUNCTIONS(INT)
  check_eval(
      /* 5 > 2 * x */
      gt(num(5), mul(num(2),x)),
      /*  0 < 5 - 2 * x */
      lt(num(0), add(num(5), uminus(mul(num(2),x))))
    );
}

TEST_FUN(normalize_less_equal_1) {
  TERM_FUNCTIONS(INT)
  check_eval(
      /* 5 <= x */
      leq(num(5), x),
      /* 0 <  x - 4 */
      lt(num(0), add(x, num(-4)))
    );
}

TEST_FUN(normalize_less_equal_2) {
  TERM_FUNCTIONS(INT)
  check_eval(
      /* ~(5 > x) */
      neg(gt(num(5), x)),
      /* 0 <  x - 4 */
      lt(num(0), add(x, num(-4)))
    );
}

TEST_FUN(normalize_less_equal_3) {
  TERM_FUNCTIONS(INT)
  check_eval(
      /* x >= 5 */
      geq(x, num(5)),
      /* 0 <  x - 4 */
      lt(num(0), add(x, num(-4)))
    );
}

TEST_FUN(normalize_less_equal_4) {
  TERM_FUNCTIONS(INT)
  check_eval(
      /* ~(x < 5) */
      neg(lt(x, num(5))),
      /* 0 <  x - 4 */
      lt(num(0), add(x, num(-4)))
    );
}

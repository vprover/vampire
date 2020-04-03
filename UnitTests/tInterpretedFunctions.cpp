
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

#define TEST_FAIL cout << "FAIL" << endl;

#define x  TermList::var(0)
#define x1 TermList::var(1)

TermList mul(TermList lhs, TermList rhs) {
  return TermList(
      Term::create2(env.signature->addInterpretedFunction(Theory::Interpretation::REAL_MULTIPLY, "mul"), 
        lhs,
        rhs));
}

TermList uminus(TermList lhs) {
  return TermList(
      Term::create1(env.signature->addInterpretedFunction(Theory::Interpretation::REAL_UNARY_MINUS, "minus"), 
        lhs));
}

TermList add(TermList lhs, TermList rhs) {
  return TermList(
      Term::create2(env.signature->addInterpretedFunction(Theory::Interpretation::REAL_PLUS, "$sum"), 
        lhs,
        rhs));
}

TermList a() {
  unsigned f = env.signature->addFunction("a",0);
  static bool set = false;
  if (!set) {
    env.signature->getFunction(f)->setType(OperatorType::getFunctionType({},Sorts::SRT_REAL));
    set = true;
  }
  return TermList(Term::createConstant(f));
}

TermList f(TermList args) {
  unsigned f = env.signature->addFunction("f",1);
  static bool set = false;
  if (!set) {
    env.signature->getFunction(f)->setType(OperatorType::getFunctionType({ Sorts::SRT_REAL },Sorts::SRT_REAL));
    set = true;
  }
  return TermList(Term::create1(f, args));
}

TermList real(int i) {
  return TermList(theory->representConstant(RealConstantType(RationalConstantType(i))));
}

TermList real(int a, int b) {
  return TermList(theory->representConstant(RealConstantType(RationalConstantType(a,b))));
}

TermList var(int i) { 
  return TermList::var(i); 
}


Literal& gt(TermList lhs, TermList rhs) {
  return *Literal::create2(env.signature->addInterpretedPredicate(Theory::Interpretation::REAL_GREATER, "gt"),
      true, lhs,rhs);
}

Literal& eq(TermList lhs, TermList rhs) {
  return *Literal::createEquality(true, lhs, rhs, Sorts::SRT_REAL);
}

Literal& neq(TermList lhs, TermList rhs) {
  return *Literal::createEquality(false, lhs, rhs, Sorts::SRT_REAL);
}

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
      cout << a;
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
    cout << endl;
    std::cout << msg << ": ";
    dump_all(vs...);
    cout << endl;
    TEST_FAIL
  }
}

template<class A>
void check_eq(A l, A r, const char* msg, const Literal& input) {
  if (l != r) {
    cout << endl;
    std::cout << msg << ". input: " << input << "\t is: " << l << "\t expected: " << r;
    cout << endl;
    TEST_FAIL
  }
}

void check_eval(Literal& orig, bool expected) {
  auto eval = InterpretedLiteralEvaluator();

  bool constant;
  Literal* result = nullptr;
  bool constantTrue;

  auto sideConditions = Stack<Literal*>();
  auto success = eval.evaluate(&orig,constant,result,constantTrue, sideConditions);

  check(sideConditions.isEmpty(), "non-empty side condictions", sideConditions);
  check(success, "evaluation faliled");
  check(result, "result not set");
  check_eq(constant, true, "result not evaluated to constant", orig);
  check_eq(constantTrue, expected, "result not evaluated to constant", orig);
}

void check_eval(Literal& orig, const Literal& expected) {
  auto eval = InterpretedLiteralEvaluator();

  bool constant;
  Literal* result = nullptr;
  bool constantTrue;

  auto sideConditions = Stack<Literal*>();
  auto success = eval.evaluate(&orig,constant,result,constantTrue, sideConditions);

  check(sideConditions.isEmpty(), "non-empty side condictions", sideConditions);
  check(success, "evaluation faliled");
  check(result, "result not set");
  check(Indexing::TermSharing::equals(result, &expected), "unexpected evaluation", 
      orig.toString(), "\t->\t", result->toString(), "\tis not\t", expected.toString());

}


// Interpret x*2=5
TEST_FUN(rebalance_var)
{

  check_eval(
      eq(mul(real(2), x), real(5)),
      eq(real(5,2), x)
    );

  check_eval(
      eq(add(real(2), x), real(4)),
      eq(real(2), x)
    );

  check_eval(
      eq(add(real(2), x), a()),
      eq(add(a(), real(-2)), x)
    );

  // check_eval(
  //     eq(add(real(2), b()), a()),
  //     eq(add(a(), uminus(b())), x)
  //   );

}

TEST_FUN(literal_to_const)
{

  // Interpret 2.5*2=5
  check_eval(
      eq(mul(real(5,2), real(2)), real(5)),
      true 
    );

  // Interpret 2.5*2=5
  check_eval(
      eq(mul(real(5,2), real(2)), real(6)),
      false 
    );

  // Interpret 3*2 > 5
  check_eval(
      gt(mul(real(3),real(2)),real(5)),
      true
    );

  // Interpret 3*2 > 13
  check_eval(
      gt(mul(real(3),real(2)),real(13)),
      false
    );

  // Interpret 3*a > 13*a
  check_eval(
      gt(mul(real(3),a()),mul(real(13), a())),
      false
    );

  // Interpret 18*a > 13*a
  check_eval(
      gt(mul(real(18),a()),mul(real(13), a())),
      true
    );

}

// Interpret 5.0 = 2.0 * y(5.0)
TEST_FUN(rebalance_uninterpreted)
{

  check_eval(
      eq(real(5), mul(real(2),f(real(5)))),
      eq(f(real(5)), real(5,2))
    );

}

// Interpret x = -x
TEST_FUN(minus_x_eq_x)
{

  check_eval(
      eq(x, uminus(x)),
      eq(x, real(0))
    );

  check_eval(
      neq(x, uminus(x)),
      neq(x, real(0))
    );

};

// Interpret k*x = 0
TEST_FUN(k_x_eq_0)
{

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
TEST_FUN(x_gt_minus_x)
{

  check_eval(
      gt(x, uminus(x)),
      gt(x, real(0))
    );

  check_eval(
      gt(uminus(x), x),
      gt(real(0), x)
    );
};

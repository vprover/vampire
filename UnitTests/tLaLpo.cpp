/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**!  This file contains examples on how to use Test/SyntaxSugar.hpp.
 *
 * @autor Johannes Schoisswohl
 * @date 2020-04-29
 */

#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Kernel/LaLpo.hpp"
#include "Kernel/Ordering.hpp"
#include "Test/TestUtils.hpp"

//////////////////////////////////////////////////////////////////////////////// 
/////////////////////////////// HELPER FUNCTIONS /////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////// 

using namespace Test;
const LaLpo::Result Greater = LaLpo::Result::GREATER;
const LaLpo::Result Less    = LaLpo::Result::LESS;
const LaLpo::Result Equal   = LaLpo::Result::EQUAL;
const LaLpo::Result Incomp  = LaLpo::Result::INCOMPARABLE;

template<class T>
void check__(Ordering& ord, T lhs, LaLpo::Result exp, T rhs) {
  // std::cout << std::endl;
  auto check_ = [&](T lhs, LaLpo::Result exp, T rhs) {
    auto res = ord.compare(lhs,rhs);
    if (res != exp) {
      std::cout << "\r[ fail ] " << pretty(lhs) << "\t" << res << "\t" << pretty(rhs)  << "\t(expected: " << exp << " )"<< std::endl;
      exit(-1);
    } else {
      std::cout << "\r[  ok  ] " << pretty(lhs) << "\t" << res << "\t" << pretty(rhs)  << std::endl;
    }
  };
  switch (exp) {
    case Incomp:
    case Equal:
      check_(lhs, exp, rhs);
      check_(rhs, exp, lhs);
      return;
    case Greater:
      check_(lhs, Greater, rhs);
      check_(rhs, Less   , lhs);
      return;
    case Less: 
      check_(lhs, Less   , rhs);
      check_(rhs, Greater, lhs);
      return;
    default:
      ASSERTION_VIOLATION
  }
}

void check(LaLpo& ord, TermList lhs, LaLpo::Result exp, TermList rhs) 
{ check__(ord, lhs,exp,rhs); }

void check(LaLpo& ord, Literal* lhs, LaLpo::Result exp, Literal* rhs) 
{ check__(ord, lhs,exp,rhs); }

LaLpo laLpo() {

  auto funcPrec = []() -> DArray<int> {
    unsigned num = env.signature->functions();
    DArray<int> out(num);
    out.initFromIterator(getRangeIterator(0u, num));
    return out;
  };

  auto predPrec = []() -> DArray<int> {
    unsigned num = env.signature->predicates();
    DArray<int> out(num);
    out.initFromIterator(getRangeIterator(0u, num));
    return out;
  };


  return LaLpo(Precedence(funcPrec(), predPrec()));
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////// TEST CASES //////////////////////////////////
//
// How to read the test cases in this file:
//
TEST_FUN(lpo_test01) {
  DECL_DEFAULT_VARS         // <- macro to initialize some syntax sugar for creating terms over a single uninterpreted sort
  DECL_SORT(srt)            // <- declares an uniterpreted sort
  DECL_FUNC (f, {srt}, srt) // <- declares a function symbol with arity 1
  DECL_FUNC (g, {srt}, srt) // <- declares a function symbol with arity 1
  DECL_CONST(c, srt)        // <- declares a constant symbol
 
  // !!! The declaration order of function and constant symbols will define their precedence relation !!!

  auto ord = laLpo(); 

  check(ord, f(c), Less, g(c));
}
//
//
//
////////////////////////////////////////////////////////////////////////////////

TEST_FUN(lpo_test02) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_FUNC (f, {srt}, srt)
  DECL_FUNC (g, {srt}, srt)
  DECL_CONST(c, srt)

  auto ord = laLpo();

  check(ord, f(c), Less, g(g(g(g(g(c))))));
}

TEST_FUN(lpo_test03) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_FUNC (f , {srt}     , srt)
  DECL_FUNC (g , {srt}     , srt)
  DECL_FUNC (g2, {srt, srt}, srt)
  DECL_FUNC (u,  {srt}     , srt)
  DECL_CONST(a, srt)
  DECL_CONST(b, srt)
  DECL_CONST(c, srt)

  auto ord = laLpo();

  check(ord, f(x), Incomp , g(g(g(g(g(c))))));
  check(ord, f(x), Less   , g(g(g(g(g(x))))));
  check(ord, g(x), Greater, f(f(f(f(f(x))))));
  check(ord, f(x), Incomp, g(g(g(g(g(y))))));
  check(ord, f(x), Greater, x);
  check(ord, f(g2(x, c)), Greater, g2(x, c));
  check(ord, f(x), Less, g(x));
  check(ord, g(f(x)), Greater, f(g(x)));
  check(ord, a, Less,b);
  check(ord, u(g2(g(x),g(a))), Greater, u(g2(x,g(a))));
  check(ord, u(g2(g(u(x)),g(a))), Greater, u(g2(x,g(a))));
  check(ord, u(f(x)), Greater, f(x));
  check(ord, f(u(x)), Greater, f(x));
}

TEST_FUN(lpo_test04) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_FUNC(f, {srt}, srt)
  DECL_FUNC(g, {srt}, srt)
  DECL_PRED(p, {srt})

  auto ord = laLpo();

  check(ord, p(f(g(x))), Less, p(g(f(x))));
}


TEST_FUN(lpo_test05) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_PRED(r, {srt, srt})
  DECL_FUNC(g, {srt, srt}, srt)

  auto ord = laLpo();

  check(ord, r(x,y), Incomp, r(y,x));
  check(ord, g(x,y), Incomp, g(y,x));
}


TEST_FUN(lalpo_test01) {
  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Int)
  DECL_FUNC (f, {Int}, Int)
  DECL_CONST(a, Int)

  auto ord = laLpo();

  check(ord, x, Incomp, a); 

  check(ord, f(x)    , Less, 3 * f(x));
  check(ord, 5 * f(x), Greater, 3 * f(x));

  check(ord,          f(x) , Less,     f(f(x)));
  check(ord,      3 * f(x) , Less,     f(f(x)));
  check(ord,          f(x) , Less, 3 * f(f(x)));
  check(ord,      5 * f(x) , Less, 3 * f(f(x)));
  check(ord, 7 * (5 * f(x)), Less, 3 * f(f(x)));
  check(ord, 7 * (f(x) * 5), Less, 3 * f(f(x)));

  check(ord, f(x) * f(x), Greater, f(x));

  check(ord, f(a) + f(a), Less, a + f(f(a)));
  check(ord, f(a) + f(a), Less, f(f(a)) + a);
  check(ord, f(a) + x   , Incomp, a + f(x));
  check(ord, f(a) + x   , Incomp, f(x) + a);
}


TEST_FUN(lalpo_test_literals) {
  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Int)
  DECL_CONST(a, Int)
  DECL_CONST(b, Int)
  DECL_FUNC (f, {Int}, Int)
  DECL_PRED (p, {Int})

  auto ord = laLpo();

  check(ord,     f(x) > 0, Less   , 3 * f(x) > 0);
  check(ord, 5 * f(x) > 0, Greater, 3 * f(x) > 0);

  check(ord,     f(x) + a > 0, Less   , 3 * f(x) + a > 0);
  check(ord, 5 * f(x) + a > 0, Greater, 3 * f(x) + a > 0);

  check(ord,                     f(x) > 0, Less,     f(f(x)) > 0);
  check(ord,              f(x) + f(x) > 0, Less,     f(f(x)) > 0);
  check(ord,              f(a) + f(b) > 0, Less,     f(f(x)) > 0);
  check(ord,   3 * f(x)               > 0, Less,     f(f(x)) > 0);
  check(ord,   3 * f(x) + f(a) + f(b) > 0, Less,     f(f(x)) > 0);
  check(ord,   3 * f(x) + x           > 0, Less,     f(f(x)) > 0);
  check(ord,   3 * f(x) + x     + y   > 0, Less,     f(f(x)) + y > 0);
  check(ord,   3 * f(x) + x     + y   > 0, Incomp,   f(f(x))     > 0);

  // checking precedence
  check(ord, f(x) >= 0, Greater,  f(x) >  0);
  check(ord, f(x) >  0, Greater,  f(x) != 0);
  check(ord, f(x) != 0, Greater,  f(x) == 0);

  // checking multiset property for literals
  check(ord, 3 * f(x) + 5 * f(x) == 0, Greater,  8 * f(x) > 0);
  check(ord, 3 * f(x) + 5 * f(x) >= 0, Greater,  8 * f(x) > 0);
  check(ord, 3 * f(x) + 5 * f(x) >  0, Greater,  8 * f(x) > 0);
  check(ord, 3 * f(x) + 5 * f(x) != 0, Greater,  8 * f(x) > 0);
  
  // checking uninterpreted r maximal
  check(ord, p(x), Greater,  8 * f(x) >  0);
  check(ord, p(y), Greater,  8 * f(x) >  0);

}

TEST_FUN(lalpo_test_literals_numerals) {
  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Rat)
  DECL_FUNC (f, {Rat}, Rat)

  auto ord = laLpo();

  check(ord,              3 * f(x) > 0, Less   , frac(1,3) * f(x)  > 0);
  check(ord,      frac(1,5) * f(x) > 0, Greater,         5 * f(x)  > 0);

}


TEST_FUN(lalpo_bug01) {
  DECL_DEFAULT_VARS
  DECL_VAR(x0, 0); DECL_VAR(x1, 1); DECL_VAR(x2, 2); DECL_VAR(x3, 3);
  NUMBER_SUGAR(Int)
  DECL_FUNC (f, {Int,Int}, Int)
  DECL_CONST(a, Int)
  DECL_CONST(b, Int)
  DECL_CONST(c, Int)

  auto ord = laLpo();

  check(ord, x, Incomp, a); 

  check(ord, f(a + b, c), Equal, f(a + b, c));
  check(ord, f(b + a, c), Equal, f(a + b, c));

  check(ord,  f(x0 * (x1 * x3)          , x0 * (x1 * x2)),
        Less, f(x0 * (x1 * x2 + x1 * x3), x0 * (x1 * x2)) );
}

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
#include "Kernel/QKbo.hpp"
#include "Kernel/Ordering.hpp"
#include "Test/TestUtils.hpp"

//////////////////////////////////////////////////////////////////////////////// 
/////////////////////////////// HELPER FUNCTIONS /////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////// 

using namespace Test;
const QKbo::Result Greater = QKbo::Result::GREATER;
const QKbo::Result Less    = QKbo::Result::LESS;
const QKbo::Result Equal   = QKbo::Result::EQUAL;
const QKbo::Result Incomp  = QKbo::Result::INCOMPARABLE;

DArray<int> funcPrec() {
  unsigned num = env.signature->functions();
  DArray<int> out(num);
  out.initFromIterator(getRangeIterator(0u, num));
  return out;
}

DArray<int> predPrec() {
  unsigned num = env.signature->predicates();
  DArray<int> out(num);
  out.initFromIterator(getRangeIterator(0u, num));
  return out;
}

template<class T>
void check___(Ordering& ord, T lhs, QKbo::Result exp, T rhs) {
  // std::cout << std::endl;
  auto check_ = [&](T lhs, QKbo::Result exp, T rhs) {
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

void check(QKbo& ord, TermList lhs, QKbo::Result exp, TermList rhs) 
{ check___(ord, lhs,exp,rhs); }

void check(QKbo& ord, Literal* lhs, QKbo::Result exp, Literal* rhs) 
{ check___(ord, lhs,exp,rhs); }

QKbo qkbo() {
  CALL("qkbo(...)")
  return QKbo(Precedence(funcPrec(), predPrec()));
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////// TEST CASES //////////////////////////////////
//
// How to read the test cases in this file:
//
TEST_FUN(test01) {
  DECL_DEFAULT_VARS         // <- macro to initialize some syntax sugar for creating terms over a single uninterpreted sort
  DECL_SORT(srt)            // <- declares an uniterpreted sort
  DECL_FUNC (f, {srt}, srt) // <- declares a function symbol with arity 1
  DECL_FUNC (g, {srt}, srt) // <- declares a function symbol with arity 1
  DECL_CONST(c, srt)        // <- declares a constant symbol
 
  // !!! The declaration order of function and constant symbols will define their precedence relation !!!

  auto ord = qkbo(); 

  check(ord, f(c), Less, g(c));
}
//
//
//
////////////////////////////////////////////////////////////////////////////////

TEST_FUN(test02) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_FUNC (f, {srt}, srt)
  DECL_FUNC (g, {srt}, srt)
  DECL_CONST(c, srt)

  auto ord = qkbo();

  check(ord, f(c), Less, g(g(g(g(g(c))))));
}

TEST_FUN(test03) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_FUNC (f , {srt}     , srt)
  DECL_FUNC (g , {srt}     , srt)
  DECL_FUNC (g2, {srt, srt}, srt)
  DECL_FUNC (u,  {srt}     , srt)
  DECL_CONST(a, srt)
  DECL_CONST(b, srt)
  DECL_CONST(c, srt)

  auto ord = qkbo();

  check(ord, f(x), Incomp , g(g(g(g(g(c))))));
  check(ord, f(x), Less   , g(g(g(g(g(x))))));
  check(ord, g(x), Less   , f(f(f(f(f(x))))));
  check(ord, f(x), Incomp, g(g(g(g(g(y))))));
  check(ord, f(x), Greater, x);
  check(ord, f(g2(x, c)), Greater, g2(x, c));
  check(ord, f(x), Less, g(x));
  check(ord, g(f(x)), Greater, f(g(x)));
  check(ord, a, Less, b);
  check(ord, u(g2(g(  x ),g(a))), Greater, u(g2(x,g(a))));
  check(ord, u(g2(g(u(x)),g(a))), Greater, u(g2(x,g(a))));
  check(ord, u(f(x)), Greater, f(x));
  check(ord, f(u(x)), Greater, f(x));
}

TEST_FUN(test04) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_FUNC(f, {srt}, srt)
  DECL_FUNC(g, {srt}, srt)
  DECL_PRED(p, {srt})

  auto ord = qkbo();

  check(ord, p(f(g(x))), Less, p(g(f(x))));
}


TEST_FUN(test05) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_PRED(r, {srt, srt})
  DECL_FUNC(g, {srt, srt}, srt)

  auto ord = qkbo();

  check(ord, r(x,y), Incomp, r(y,x));
  check(ord, g(x,y), Incomp, g(y,x));
}


TEST_FUN(latest01) {
  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Int)
  DECL_FUNC (f, {Int}, Int)
  DECL_CONST(a, Int)
  DECL_CONST(b, Int)
  DECL_CONST(c, Int)
  DECL_CONST(d, Int)

  auto ord = qkbo();

  check(ord, x, Incomp, a); 
  check(ord, x + y, Incomp, y + x); 
  check(ord, x + y, Incomp, x + y); 

  check(ord,     f(x), Less,    3 * f(x));
  check(ord, 5 * f(x), Greater, 3 * f(x));

  check(ord,          f(x) , Less,     f(f(x)));
  check(ord,      3 * f(x) , Less,     f(f(x)));
  check(ord,          f(x) , Less, 3 * f(f(x)));
  check(ord,      5 * f(x) , Less, 3 * f(f(x)));
  // check(ord, 7 * (5 * f(x)), Less, 3 * f(f(x)));
  // check(ord, 7 * (f(x) * 5), Less, 3 * f(f(x)));

  check(ord, f(x) * f(x), Greater, f(x));

  check(ord, f(a) + f(a), Incomp, a + f(f(a)));
  check(ord, f(a) + f(a), Incomp, f(f(a)) + a);
  check(ord, f(a) + x   , Incomp, a + f(x));
  check(ord, f(a) + x   , Incomp, f(x) + a);
  check(ord, a + b + c + d + x, Incomp, f(x));
  check(ord, a + b + c + d    , Less, f(x));
}


TEST_FUN(latest_literals) {
  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Int)
  DECL_CONST(a, Int)
  DECL_CONST(b, Int)
  DECL_FUNC (f, {Int}, Int)
  DECL_PRED (p, {Int})

  auto ord = qkbo();

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

TEST_FUN(latest_literals_numerals) {
  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Rat)
  DECL_FUNC (f, {Rat}, Rat)

  auto ord = qkbo();

  check(ord,              3 * f(x) > 0, Less   , frac(1,3) * f(x)  > 0);
  check(ord,      frac(1,5) * f(x) > 0, Greater,         5 * f(x)  > 0);

}

TEST_FUN(misc01) {
  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Int)
  DECL_FUNC (f, {Int,Int}, Int)
  DECL_FUNC (g, {Int}, Int)
  DECL_CONST(a, Int)
  DECL_CONST(b, Int)
  DECL_CONST(c, Int)

  auto ord = qkbo();

  check(ord, x, Incomp, a); 

  check(ord, f(a + b, c), Equal, f(a + b, c));
  check(ord, f(b + a, c), Equal, f(a + b, c));
  check(ord, f(g(x) + a, c), Equal, f(a + g(x), c));
}

TEST_FUN(misc02) {
  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Int)
  DECL_FUNC (f, {Int}, Int)

  auto ord = qkbo();

  check(ord, f(x + y), Incomp, x);
}


TEST_FUN(normal_form01) {
  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Real)
  DECL_CONST(a, Real)
  DECL_CONST(b, Real)
  DECL_CONST(c, Real)
  DECL_FUNC (f, {Real}, Real)

  ASS_EQ(QKbo::sigmaNf(2 * a + b), SigmaNf(1, {
        SignedTerm::pos(a),
        SignedTerm::pos(a),
        SignedTerm::pos(b),
      }));

  ASS_EQ(QKbo::sigmaNf(2 * a + 0 * b), SigmaNf(1, {
        SignedTerm::pos(a),
        SignedTerm::pos(a),
        SignedTerm::zero(b),
      }));

  ASS_EQ(QKbo::sigmaNf(2 * a + 0 * a), SigmaNf(1, {
        SignedTerm::pos(a),
        SignedTerm::pos(a),
      }));

  ASS_EQ(QKbo::sigmaNf(2 * a + 1 * a), SigmaNf(1, {
        SignedTerm::pos(a),
        SignedTerm::pos(a),
        SignedTerm::pos(a),
      }));

  ASS_EQ(QKbo::sigmaNf(2 * a + -3 * a), SigmaNf(1, {
        SignedTerm::neg(a),
      }));

  ASS_EQ(QKbo::sigmaNf(2 * a + -4 * a), SigmaNf(1, {
        SignedTerm::neg(a),
        SignedTerm::neg(a),
      }));

  ASS_EQ(QKbo::sigmaNf(frac(1, 2) * a +  b), SigmaNf(2, {
        SignedTerm::pos(a),
        SignedTerm::pos(b),
        SignedTerm::pos(b),
      }));

  // Problem:
  //
  // -f(x) + f(y) > f(x)
  // but
  // -f(a) + f(a) < f(a)
  // since { 0 f(a) } < { +f(a) }

}

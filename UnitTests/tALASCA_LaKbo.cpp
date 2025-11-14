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
 * @author Johannes Schoisswohl
 * @date 2020-04-29
 */

#include "Debug/Assertion.hpp"
#include "Test/AlascaTestUtils.hpp"
#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Kernel/ALASCA/Ordering.hpp"
#include "Kernel/Ordering.hpp"
#include "Test/TestUtils.hpp"

//////////////////////////////////////////////////////////////////////////////// 
/////////////////////////////// HELPER FUNCTIONS /////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////// 

using namespace Test;
const Ordering::Result Greater = Ordering::Result::GREATER;
const Ordering::Result Less    = Ordering::Result::LESS;
const Ordering::Result Equal   = Ordering::Result::EQUAL;
const Ordering::Result Incomp  = Ordering::Result::INCOMPARABLE;
using namespace Kernel;
using LaKbo = LiteralOrdering<LAKBO>;

template<class T>
void check___(Ordering& ord, T lhs, Ordering::Result exp, T rhs, bool silent) {
  // std::cout << std::endl;
  auto check_ = [&](T lhs, Ordering::Result exp, T rhs) {
    auto res = ord.compare(lhs,rhs);
    if (res != exp) {
      std::cout << "\r[ fail ] " << pretty(lhs) << "\t" << res << "\t" << pretty(rhs)  << "\t(expected: " << exp << " )"<< std::endl;
      std::cout << "\r[  ord ] " << std::endl;
      ord.show(std::cout);
      ASSERTION_VIOLATION
    } else {
      if (!silent)
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

void check(LaKbo& ord, TermList lhs, LaKbo::Result exp, TermList rhs, bool silent = false)
{ check___(ord, lhs,exp,rhs, silent); }

void check(LaKbo& ord, Literal* lhs, LaKbo::Result exp, Literal* rhs, bool silent = false) 
{ check___(ord, lhs,exp,rhs, silent); }

void check_in_different_contexts(LaKbo& ord, TermList l, LaKbo::Result exp, TermList r, PredSugar ctxt, FuncSugar func) 
{ 

  check(ord, l, exp, r);
  check(ord, func(l), exp, func(r));
  check(ord, ctxt(l), exp, ctxt(r));
  check(ord, l >= 0, exp, r >= 0);
  check(ord, l >  0, exp, r >  0);
  check(ord, l == 0, exp, r == 0);
  check(ord, l != 0, exp, r != 0);
}

LaKbo& lakbo(bool rand = false) { return *new LaKbo(LAKBO(KBO::testKBO(rand, /* qkboPrec */ true), Lib::make_shared(InequalityNormalizer()))); }


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////// TEST CASES //////////////////////////////////
//
// How to read the test cases in this file:
//
TEST_FUN(uninterpreted_terms_01) {
  DECL_DEFAULT_VARS         // <- macro to initialize some syntax sugar for creating terms over a single uninterpreted sort
  DECL_SORT(srt)            // <- declares an uniterpreted sort
  DECL_FUNC (f, {srt}, srt) // <- declares a function symbol with arity 1
  DECL_FUNC (g, {srt}, srt) // <- declares a function symbol with arity 1
  DECL_CONST(c, srt)        // <- declares a constant symbol
 
  // !!! The declaration order of function and constant symbols will define their precedence relation !!!

  auto& ord = lakbo(); 

  check(ord, f(c), Less, g(c));
}
//
//
//
////////////////////////////////////////////////////////////////////////////////

TEST_FUN(uninterpreted_terms_02) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_FUNC (f, {srt}, srt)
  DECL_FUNC (g, {srt}, srt)
  DECL_CONST(c, srt)

  auto& ord = lakbo();

  check(ord, f(c), Less, g(g(g(g(g(c))))));
}

TEST_FUN(uninterpreted_terms_03) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_FUNC (f , {srt}     , srt)
  DECL_FUNC (g , {srt}     , srt)
  DECL_FUNC (g2, {srt, srt}, srt)
  DECL_FUNC (u,  {srt}     , srt)
  DECL_CONST(a, srt)
  DECL_CONST(b, srt)
  DECL_CONST(c, srt)

  auto& ord = lakbo();

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

TEST_FUN(uninterpreted_terms_04) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_FUNC(f, {srt}, srt)
  DECL_FUNC(g, {srt}, srt)
  DECL_PRED(p, {srt})

  auto& ord = lakbo();

  check(ord, p(f(g(x))), Less, p(g(f(x))));
}


TEST_FUN(uninterpreted_terms_05) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_PRED(r, {srt, srt})
  DECL_PRED(g, {srt, srt})
  auto& ord = lakbo();

  check(ord, r(x,y), Incomp, r(y,x));
  check(ord, g(x,y), Incomp, g(y,x));
}


TEST_FUN(interpreted_terms_01) {
  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Int)
  DECL_FUNC (f, {Int}, Int)
  DECL_CONST(a, Int)
  DECL_CONST(b, Int)
  DECL_CONST(c, Int)
  DECL_CONST(d, Int)

  auto& ord = lakbo();

  check(ord, x, Incomp, a); 
  check(ord, a + b, Equal, b + a); 
  check(ord, x + y, Equal, y + x); 
  // check(ord, x + y, Incomp, x + y); 

  check(ord,     f(x), Less,    3 * f(x));
  check(ord, 5 * f(x), Greater, 3 * f(x));

  check(ord,          f(x) , Less,     f(f(x)));
  check(ord,      3 * f(x) , Less,     f(f(x)));
  check(ord,          f(x) , Less, 3 * f(f(x)));
  check(ord,      5 * f(x) , Less, 3 * f(f(x)));
  // check(ord, 7 * (5 * f(x)), Less, 3 * f(f(x)));
  // check(ord, 7 * (f(x) * 5), Less, 3 * f(f(x)));

  check(ord, f(x) * f(x), Greater, f(x));

  check(ord, f(a) + f(a), Less, a + f(f(a)));
  check(ord, f(a) + f(a), Less, f(f(a)) + a);
  check(ord, f(a) + x   , Incomp, a + f(x));
  check(ord, f(a) + x   , Incomp, f(x) + a);
  check(ord, a + b + c + d + x, Incomp, f(x));
  check(ord, a + b + c + d    , Less, f(x));
}


TEST_FUN(interpreted_literals_01) {
  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Int)
  DECL_CONST(a, Int)
  DECL_CONST(b, Int)
  DECL_FUNC (f, {Int}, Int)
  DECL_PRED (p, {Int})


  auto& ord = lakbo();

  check(ord,     f(x) + a > 0, Less   , 3 * f(x) + a > 0);
  check(ord, 5 * f(x) + a > 0, Greater, 3 * f(x) + a > 0);

  check(ord,                     f(x) > 0, Less,     f(f(x)) > 0);
  check(ord,              f(x) + f(x) > 0, Less,     f(f(x)) > 0);
  check(ord,              100  * f(x) > 0, Less,     f(f(x)) > 0);
  check(ord,              f(a) + f(b) > 0, Less,     f(f(x)) > 0);
  check(ord,   3 * f(x)               > 0, Less,     f(f(x)) > 0);
  check(ord,   3 * f(x) + f(a) + f(b) > 0, Less,     f(f(x)) > 0);
  check(ord,   3 * f(x) + x           > 0, Less,     f(f(x)) > 0);
  check(ord,   3 * f(x) + x     + y   > 0, Incomp,   f(f(x))     > 0);

  check(ord,             f(x) + f(x) > 0, Equal,  2 * f(x) > 0);
  check(ord,    13 * f(x) + 2 * f(x) > 0, Equal, 15 * f(x) > 0);

  check(ord, f(x) >= 0, Greater,  f(x) == 0);
  check(ord, f(x) >  0, Greater,  f(x) == 0);
  check(ord, f(x) != 0, Greater,  f(x) == 0);

  check(ord, 3 * f(x) + 5 * f(x) == 0, Less   ,  8 * f(x) > 0);
  check(ord, 3 * f(x) + 5 * f(x) >= 0, Greater,  8 * f(x) == 0);
  
  // checking uninterpreted r maximal
  check(ord, p(x), Greater,  8 * f(x) >  0);
  check(ord, p(y), Greater,  8 * f(x) >  0);

  // tricky 
  check(ord,   3 * f(a) + a +      b   > 0, Less,    f(f(a)) +      b   > 0);
  check(ord,   3 * f(a) + a + -f(f(a)) > 0, Greater, f(f(a)) + -f(f(a)) > 0);
  check(ord,   3 * f(x) + x +      y   > 0, Less  ,  f(f(x)) +      y   > 0);
}

TEST_FUN(misc01) {
  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Int)
  DECL_FUNC (f, {Int,Int}, Int)
  DECL_FUNC (g, {Int}, Int)
  DECL_CONST(a, Int)
  DECL_CONST(b, Int)
  DECL_CONST(c, Int)

  auto& ord = lakbo();

  check(ord, x, Incomp, a); 

  check(ord, f(a + b, c), Equal, f(a + b, c));
  check(ord, f(b + a, c), Equal, f(a + b, c));
  check(ord, f(g(x) + a, c), Equal, f(a + g(x), c));
}

TEST_FUN(misc02) {
  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Int)
  DECL_FUNC (f, {Int}, Int)

  auto& ord = lakbo();

  check(ord, f(x + y), Incomp, x);
}


TEST_FUN(tricky_01) {
  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Real)
  DECL_FUNC (f, {Real}, Real)
  DECL_FUNC (g, {Real, Real}, Real)
  DECL_PRED (p, {Real})
  DECL_CONST(a, Real)
  DECL_CONST(b, Real)

  auto& ord = lakbo();
  check_in_different_contexts(ord, f(g(a,a)) + 2 * f(a) - f(a), Less   , f(g(a,a)) + 2 * f(a), p , f );
  check_in_different_contexts(ord, f(g(a,b)) + 2 * f(a) - f(b), Greater, f(g(a,b)) + 2 * f(a), p , f );
  check_in_different_contexts(ord, f(g(x,y)) + 2 * f(x) - f(y), Greater, f(g(x,y)) + 2 * f(x), p , f ); 
}

TEST_FUN(tricky_02) {

  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Real)
  DECL_FUNC (f, {Real}, Real)
  DECL_FUNC (g, {Real, Real}, Real)
  DECL_PRED (p, {Real})
  DECL_CONST(a, Real)
  DECL_CONST(b, Real)
  DECL_CONST(c, Real)

  auto& ord = lakbo();


  check(ord, f(g(a,  a )) - 2 * f(a) + f(  a ) , Greater , f(g(a,  a )) + 100 * f(a));
  check(ord, f(g(a,f(a))) - 2 * f(a) + f(f(a)) , Greater , f(g(a,f(a))) + 100 * f(a));
  #ifdef TRICKY_IMPLEMENTED
  check(ord, f(g(x,  y )) - 2 * f(x) + f(  y ) , Greater , f(g(x,  y )) + 100 * f(x));
  #endif

  check_in_different_contexts(ord, f(g(a,  a )) + 2 * f(a) - f(  a ), Less   , f(g(a,  a )) + 100 * f(a), p,f);
  check_in_different_contexts(ord, f(g(a,f(a))) + 2 * f(a) - f(f(a)), Greater, f(g(a,f(a))) + 100 * f(a), p,f);
  #ifdef TRICKY_IMPLEMENTED
  check_in_different_contexts(ord, f(g(x,  y )) + 2 * f(x) - f(  y ), Incomp , f(g(x,  y )) + 100 * f(x), p,f);
  #endif

  check_in_different_contexts(ord, f(g(a,a)) + 2 * f(a) - f(a) + c, Greater, f(g(a,a)) + 2 * f(a) - f(a), p,f);
  check_in_different_contexts(ord, f(g(a,b)) + 2 * f(a) - f(b) + c, Greater, f(g(a,b)) + 2 * f(a) - f(b), p,f);
  #ifdef TRICKY_IMPLEMENTED
  check_in_different_contexts(ord, f(g(x,y)) + 2 * f(x) - f(y) + c, Greater, f(g(x,y)) + 2 * f(x) - f(y), p,f);
  #endif

}

TEST_FUN(uninterpreted_predicates) {

  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Real)
  DECL_CONST(a, Real)
  DECL_CONST(b, Real)
  DECL_FUNC (f, {Real}, Real)
  // DECL_FUNC (g, {Real, Real}, Real)
  DECL_PRED (p, {Real, Real})
  DECL_PRED (q, {Real})

  auto& ord = lakbo();

  check(ord, f(a), Greater, a );

  // lex comparison
  check(ord, p(b, f(a)), Greater, p(b, a) );
  check(ord, p(f(a), b), Greater, p(a, f(a)) );
  check(ord, p(f(a), b), Greater, p(a, f(b)) );

  // sign comparison
  check(ord, ~p(b, f(a)), Greater, p(b, f(a)) );

  // precedence comparison
  check(ord,  p(b, f(a)), Less,  q(b) );
  check(ord,  p(b, f(a)), Less, ~q(b) );
  check(ord, ~p(b, f(a)), Less,  q(b) );
  check(ord, ~p(b, f(a)), Less, ~q(b) );

  // compare interpretd vs uninterpreted
  check(ord, 3 * f(a) + b + f(b) >  0, Less,  p(a,b) );
  check(ord, 3 * f(a) + b + f(b) >  0, Less, ~p(a,b) );
  check(ord, 3 * f(a) + b + f(b) >= 0, Less,  p(a,b) );
  check(ord, 3 * f(a) + b + f(b) >= 0, Less, ~p(a,b) );
  check(ord, 3 * f(a) + b + f(b) != 0, Less,  p(a,b) );
  check(ord, 3 * f(a) + b + f(b) != 0, Less, ~p(a,b) );
  check(ord, 3 * f(a) + b + f(b) == 0, Less,  p(a,b) );
  check(ord, 3 * f(a) + b + f(b) == 0, Less, ~p(a,b) );
}

TEST_FUN(atoms_comparison_two_sorts) {

  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Real)
  DECL_SORT(alpha)
  DECL_CONST(a0, Real)
  DECL_FUNC (f0, {Real}, Real)
  DECL_FUNC (g0, {alpha}, Real)

  DECL_CONST(a1, alpha)
  DECL_FUNC (f1, {alpha}, alpha)
  DECL_FUNC (g1, {Real}, alpha)


  auto& ord = lakbo();

  check(ord, g0(a1), Greater, a1);
  check(ord, g0(f1(x)), Greater, x );

  check(ord, g1(f0(a0)) == a1, Greater, f0(a0) - a0 == 0 );
  check(ord, g1(f0(a0)) == a1, Greater, f0(a0) - a0 != 0 );
  check(ord, g1(f0(a0)) == a1, Greater, f0(a0) == 0 );
  check(ord, g1(f0(a0)) == a1, Greater, f0(a0) == 0 );
  check(ord, g1(f0(a0)) == a1, Greater, 2 * f0(a0) >= 0 );
  check(ord, g1(f0(a0)) == a1, Greater, 2 * f0(a0) >  0 );

  check(ord, g1(f0(a0)) != a1, Greater, f0(a0) - a0 == 0 );
  check(ord, g1(f0(a0)) != a1, Greater, f0(a0) - a0 != 0 );
  check(ord, g1(f0(a0)) != a1, Greater, f0(a0) == 0 );
  check(ord, g1(f0(a0)) != a1, Greater, f0(a0) == 0 );
  check(ord, g1(f0(a0)) != a1, Greater, 2 * f0(a0) >= 0 );
  check(ord, g1(f0(a0)) != a1, Greater, 2 * f0(a0) >  0 );

  check(ord, f1(a1) == a1, Less, g0(f1(f1(a1))) + f0(a0) == 0 );
  check(ord, f1(a1) == a1, Less, g0(f1(f1(a1))) + f0(a0) != 0 );
  check(ord, f1(a1) == a1, Less, g0(f1(f1(a1))) + f0(a0) == 0 );
  check(ord, f1(a1) == a1, Less, g0(f1(f1(a1))) + f0(a0) != 0 );
  check(ord, f1(a1) == a1, Less, g0(f1(f1(a1))) + f0(a0) >  0 );
  check(ord, f1(a1) == a1, Less, g0(f1(f1(a1))) + f0(a0) >= 0 );

  check(ord, f1(a1) != a1, Less, g0(f1(f1(a1))) + f0(a0) == 0 );
  check(ord, f1(a1) != a1, Less, g0(f1(f1(a1))) + f0(a0) != 0 );
  check(ord, f1(a1) != a1, Less, g0(f1(f1(a1))) + f0(a0) == 0 );
  check(ord, f1(a1) != a1, Less, g0(f1(f1(a1))) + f0(a0) != 0 );
  check(ord, f1(a1) != a1, Less, g0(f1(f1(a1))) + f0(a0) >  0 );
  check(ord, f1(a1) != a1, Less, g0(f1(f1(a1))) + f0(a0) >= 0 );

}

TEST_FUN(bug01) {

  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Real)
  DECL_CONST(a, Real)
  // DECL_CONST(b, Real)
  // DECL_CONST(c, Real)
  DECL_FUNC (f, {Real}, Real)
  auto& ord = lakbo();

  check(ord, f(f(a)) - f(f(a)) > 0, Less   , f(f(a)) > 0);
}

TEST_FUN(bug02) {

  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Real)

  auto& ord = lakbo(/* rand */ false);

  DECL_CONST(a, Real)
  DECL_CONST(b, Real)
  DECL_CONST(c, Real)

  check(ord, c, Greater, -floor(frac(1,2) * floor(b) + frac(1,2) * floor(a)) + -floor(frac(1,2) + frac(1,2) * floor(b) + frac(1,2) * floor(a)));
}


TEST_FUN(bug03) {

  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Rat)
  mkAlascaSyntaxSugar(RatTraits{});
  DECL_CONST(a, Rat)
  DECL_FUNC (g, {Rat, Rat}, Rat)
  auto& ord = lakbo();

  check(ord, g(a,a), Incomp , frac(-1,2) * g(x,y));
}

TEST_FUN(numerals) {

  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Real)
  auto& ord = lakbo();

  check(ord,  num(1), Equal, num(1));
  check(ord,  num(0), Equal, num(0));
  check(ord,  num(0) * 10, Equal, num(0));

  check(ord,  num(3), Greater, num(1));
  check(ord,  num(-3), Greater, num(1));
  check(ord,  num(-3), Greater, num(3));
  check(ord,  num(-3) + 2, Greater, num(3));
  check(ord,  num(3) + -2, Less, num(3));
  check(ord,  num(2), Greater, num(1));
  check(ord,  num(0), Less, num(1));
  check(ord,  num(1), Greater, num(0));

  check(ord,  frac(1,2), Greater, num(1));
  check(ord,  frac(1,3), Greater, frac(1,2));
  check(ord,  frac(1,3), Less, -frac(1,2));
  check(ord,  frac(2,3), Greater, frac(1,3));
  check(ord,  frac(1,4), Greater, frac(2,3));
  {
    NUMBER_SUGAR(Rat)
    check(ord,  num(2), Greater, num(1));
  }
   {
    NUMBER_SUGAR(Int)
    check(ord,  num(2), Greater, num(1));
  }
 
}


TEST_FUN(eq_equiv) {

  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Real)
  DECL_CONST(a, Real)
  DECL_CONST(b, Real)
  // DECL_CONST(c, Real)
  DECL_FUNC (f, {Real}, Real)
  auto& ord = lakbo();

  check(ord,  f(a) - f(b) == 0, Equal, f(b) - f(a) == 0);
  check(ord, -f(a) - f(b) == 0, Equal, f(a) + f(b) == 0);
  check(ord,  f(a) + f(b) == 0, Equal   , -f(a) - f(b) == 0);
}

TEST_FUN(var_equalities) {

  DECL_DEFAULT_VARS
  DECL_SORT(s1)
  DECL_SORT(s2)
  auto& ord = lakbo();
  DECL_VAR(x0, 0)
  DECL_VAR(x1, 0)
  x0.sort(s1);
  x1.sort(s2);

  check(ord,  x0 == x0, Less, x1 == x1);
  check(ord,  x0 != x0, Less, x1 != x1);
}


TEST_FUN(ineq_diseq) {

  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Real)
  DECL_CONST(a, Real)
  DECL_CONST(b, Real)
  // DECL_CONST(c, Real)
  DECL_FUNC (f, {Real}, Real)
  auto& ord = lakbo();

  check(ord,  f(a) - f(b) != 0, Greater,  f(a) - f(b) > 0);
  check(ord, -f(a) + f(b) != 0, Greater, -f(a) + f(b) > 0);
}

TEST_FUN(check_one_smallest) {

  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Real)


  TermList one = num(1);
  (void) one;
  DECL_CONST(a, Real)
  DECL_CONST(b, Real)
  DECL_CONST(c, Real)
  auto& ord = lakbo();

  check(ord, num(1), Less, a);
  check(ord, num(1), Less, b);
  check(ord, num(1), Less, c);
}

TEST_FUN(check_one_smallest_2) {

  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Real)


  DECL_CONST(a, Real)
  DECL_CONST(b, Real)
  DECL_CONST(c, Real)
  auto& ord = lakbo();

  check(ord, num(1), Less, a);
  check(ord, num(1), Less, b);
  check(ord, num(1), Less, c);
}

TEST_FUN(check_numerals_smallest) {

  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Real)


  DECL_CONST(a, Real)
  DECL_CONST(b, Real)
  DECL_CONST(c, Real)

  for (auto i = 0; i < 1000; i++) {
    auto& ord = lakbo(/* rand */ true);

    check(ord, num(1), Less, a, /* silent */ true);
    check(ord, num(1), Less, b, /* silent */ true);
    check(ord, num(1), Less, c, /* silent */ true);
  }

  for (auto i = 0; i < 1000; i++) {
    auto& ord = lakbo(/* rand */ true);

    auto num = frac(Random::getInteger(1<<30), Random::getInteger(1<<30));
    check(ord, num, Less, a, /* silent */ true);
    check(ord, num, Less, b, /* silent */ true);
    check(ord, num, Less, c, /* silent */ true);
  }


}

TEST_FUN(bug_non_linear_1) {
  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Real)
  auto& ord = lakbo(/* rand */ false);
  DECL_CONST(a, Real)
  DECL_CONST(b, Real)
  check(ord, a * (1 + a), Greater, a * a);
  check(ord, a * a, Greater, a);
  check(ord, b * (a * a), Greater, b * a);
}

TEST_FUN(bug_non_linear_2) {
  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Real)
  auto& ord = lakbo(/* rand */ false);
  DECL_CONST(a, Real)
  DECL_CONST(b, Real)

  auto l1 = 0 == b* (-x + (a*a) + x);
  auto l2 = 0 == b*(a*a);
  check(ord, l1, Equal, l2);
}

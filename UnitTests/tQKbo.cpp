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
#include "Kernel/QKbo.hpp"
#include "Kernel/Ordering.hpp"
#include "Test/TestUtils.hpp"

//////////////////////////////////////////////////////////////////////////////// 
/////////////////////////////// HELPER FUNCTIONS /////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////// 

#define ENABLE_ZERO_REMOVAL 1

using namespace Test;
const QKbo::Result Greater = QKbo::Result::GREATER;
const QKbo::Result Less    = QKbo::Result::LESS;
const QKbo::Result Equal   = QKbo::Result::EQUAL;
const QKbo::Result Incomp  = QKbo::Result::INCOMPARABLE;
using namespace Kernel;

DArray<int> funcPrec() {
  unsigned num = env.signature->functions();
  DArray<int> out(num);
  out.initFromIterator(getRangeIterator(0u, num));
  return out;
}

auto ict(int i) { return IntegerConstantType(i); }

DArray<int> predPrec() {
  unsigned num = env.signature->predicates();
  DArray<int> out(num);
  out.initFromIterator(getRangeIterator(0u, num));
  return out;
}

template<class T>
void check___(Ordering& ord, T lhs, QKbo::Result exp, T rhs, bool silent) {
  // std::cout << std::endl;
  auto check_ = [&](T lhs, QKbo::Result exp, T rhs) {
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

void check(QKbo& ord, TermList lhs, QKbo::Result exp, TermList rhs, bool silent = false)
{ check___(ord, lhs,exp,rhs, silent); }

void check(QKbo& ord, Literal* lhs, QKbo::Result exp, Literal* rhs, bool silent = false) 
{ check___(ord, lhs,exp,rhs, silent); }

void check_in_different_contexts(QKbo& ord, TermList l, QKbo::Result exp, TermList r, PredSugar ctxt, FuncSugar func) 
{ 

  check(ord, l, exp, r);
  check(ord, func(l), exp, func(r));
  check(ord, ctxt(l), exp, ctxt(r));
  check(ord, l >= 0, exp, r >= 0);
  check(ord, l >  0, exp, r >  0);
  check(ord, l == 0, exp, r == 0);
  check(ord, l != 0, exp, r != 0);
}

QKbo& qkbo(bool rand = false) {
  Problem p;
  env.options->resolveAwayAutoValues0();
  env.options->resolveAwayAutoValues(p);
  auto n = Lib::make_shared(InequalityNormalizer());
  return *new QKbo(KBO::testKBO(rand, /* qkboPrec */ true), n);
}


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

  auto& ord = qkbo(); 

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

  auto& ord = qkbo();

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

  auto& ord = qkbo();

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

  auto& ord = qkbo();

  check(ord, p(f(g(x))), Less, p(g(f(x))));
}


TEST_FUN(uninterpreted_terms_05) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_PRED(r, {srt, srt})
  DECL_PRED(g, {srt, srt})
  auto& ord = qkbo();

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

  auto& ord = qkbo();

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

  auto& ord = qkbo();

  check(ord,     f(x) > 0, Less   , 3 * f(x) > 0);
  check(ord, 5 * f(x) > 0, Greater, 3 * f(x) > 0);

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
  check(ord,   3 * f(x) + x +      y   > 0, Incomp,  f(f(x)) +      y   > 0);
}

TEST_FUN(misc01) {
  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Int)
  DECL_FUNC (f, {Int,Int}, Int)
  DECL_FUNC (g, {Int}, Int)
  DECL_CONST(a, Int)
  DECL_CONST(b, Int)
  DECL_CONST(c, Int)

  auto& ord = qkbo();

  check(ord, x, Incomp, a); 

  check(ord, f(a + b, c), Equal, f(a + b, c));
  check(ord, f(b + a, c), Equal, f(a + b, c));
  check(ord, f(g(x) + a, c), Equal, f(a + g(x), c));
}

TEST_FUN(misc02) {
  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Int)
  DECL_FUNC (f, {Int}, Int)

  auto& ord = qkbo();

  check(ord, f(x + y), Incomp, x);
}

#define SIGNED_ATOM_TEST_FUNS                                                             \
  auto& ord = qkbo();                                                                     \
                                                                                          \
  auto signedAtoms = [&](auto t) -> Option<Recycled<SignedAtoms>>                         \
    { return ord.template signedAtoms<RealTraits>(t); };                                  \
                                                                                          \
  auto none = Option<Recycled<SignedAtoms>>();                                            \
  auto some = [&](int i, Stack<SignedTerm> ts)                                            \
  {                                                                                       \
    Recycled<SignedAtoms> at;                                                             \
    at->weight = ict(i);                                                                  \
    at->elems = MultiSet<SignedTerm>(std::move(ts));                                      \
    return Option<Recycled<SignedAtoms>>(std::move(at));                                  \
  };                                                                                      \


TEST_FUN(normal_subsafe) {
  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Real)
  DECL_CONST(a, Real)
  // DECL_CONST(c, Real)
  DECL_FUNC (f, {Real}, Real)

  SIGNED_ATOM_TEST_FUNS

  ASS_EQ(signedAtoms(frac(1,2) * x + 7 * a), none);
  ASS_EQ(signedAtoms( x +  7 * a), none);
  ASS_EQ(signedAtoms(-x +  7 * a), none);
  ASS_EQ(signedAtoms( x + -7 * a), none);
  ASS_EQ(signedAtoms(-x + -7 * a), none);
  ASS_EQ(signedAtoms(-x + 2 * x), some(1, { SignedTerm::pos(x) }));
  ASS_EQ(signedAtoms(-f(x) + 2 * f(a)), none);
  ASS_EQ(signedAtoms(f(x) + 2 * f(a)), some(1, { 
        SignedTerm::pos(f(x)),
        SignedTerm::pos(f(a)),
        SignedTerm::pos(f(a)),
  }));
  ASS_EQ(signedAtoms(-f(x) + -2 * f(a)), some(1, { 
        SignedTerm::neg(f(x)),
        SignedTerm::neg(f(a)),
        SignedTerm::neg(f(a)),
  }));
  ASS_EQ(signedAtoms(-f(a) + 2 * f(a)), some(1, { SignedTerm::pos(f(a)) }));


  // ASS_EQ(signedAtoms(f(frac(1,2) * x + 7 * a)), none);
  // ASS_EQ(signedAtoms(f( x +  7 * a)), none);
  // ASS_EQ(signedAtoms(f(-x +  7 * a)), none);
  // ASS_EQ(signedAtoms(f( x + -7 * a)), none);
  // ASS_EQ(signedAtoms(f(-x + -7 * a)), none);
  // ASS_EQ(signedAtoms(f(-x + 2 * x)), some(1, { SignedTerm::pos(f(x)) }));
  // ASS_EQ(signedAtoms(f(-f(x) + 2 * f(a))), none);
  // ASS_EQ(signedAtoms(f( f(x) + 2 * f(a))), some(1, { SignedTerm::pos(f( f(x) + 2 * f(a))), }));
  // ASS_EQ(signedAtoms(f(-f(x) + -2 * f(a))), some(1, { 
  //       SignedTerm::pos(f(-f(x) + -2 * f(a))),
  // }));
  // ASS_EQ(signedAtoms(-f(a) + 2 * f(a)), some(1, { SignedTerm::pos(f(a)) }));


}

TEST_FUN(normal_form_lcm) {
  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Real)
  DECL_CONST(a, Real)
  DECL_CONST(b, Real)
  // DECL_CONST(c, Real)
  // DECL_FUNC (f, {Real}, Real)

  SIGNED_ATOM_TEST_FUNS

  ASS_EQ(signedAtoms(frac(1,2) * a + b), 
      some(2, {
        SignedTerm::pos(a),
        SignedTerm::pos(b),
        SignedTerm::pos(b),
      }));

  ASS_EQ(signedAtoms(frac(1,2) * a + -b), 
      some(2, {
        SignedTerm::pos(a),
        SignedTerm::neg(b),
        SignedTerm::neg(b),
      }));

  ASS_EQ(signedAtoms(frac(-1,2) * a + -b), 
      some(2, {
        SignedTerm::neg(a),
        SignedTerm::neg(b),
        SignedTerm::neg(b),
      }));

  ASS_EQ(signedAtoms(frac(1,-2) * a + -b), 
      some(2, {
        SignedTerm::neg(a),
        SignedTerm::neg(b),
        SignedTerm::neg(b),
      }));

  ASS_EQ(signedAtoms(frac(-1,2) * a + b), 
      some(2, {
        SignedTerm::neg(a),
        SignedTerm::pos(b),
        SignedTerm::pos(b),
      }));

  ASS_EQ(signedAtoms(frac(1,2) * a + frac(1,4) * b), 
      some(4, {
        SignedTerm::pos(a),
        SignedTerm::pos(a),
        SignedTerm::pos(b),
      }));

  ASS_EQ(signedAtoms(-1 * a + -1 * b), 
      some(1, {
        SignedTerm::neg(a),
        SignedTerm::neg(b),
      }));

  ASS_EQ(signedAtoms(-1 * a + -2 * b), 
      some(1, {
        SignedTerm::neg(a),
        SignedTerm::neg(b),
        SignedTerm::neg(b),
      }));

  // ASS_EQ(signedAtoms(frac(1,2) * a + frac(0,4) * b), 
  // some(2, {
  //       SignedTerm::pos(a),
  //       SignedTerm::zero(b),
  //     }));

}



TEST_FUN(tricky_01) {

  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Real)
  DECL_FUNC (f, {Real}, Real)
  DECL_FUNC (g, {Real, Real}, Real)
  DECL_PRED (p, {Real})
  DECL_CONST(a, Real)
  DECL_CONST(b, Real)

  auto& ord = qkbo();

  check_in_different_contexts(ord, f(g(a,a)) + 2 * f(a) - f(a), Less   , f(g(a,a)) + 2 * f(a), p , f );
  check_in_different_contexts(ord, f(g(a,b)) + 2 * f(a) - f(b), Greater, f(g(a,b)) + 2 * f(a), p , f );
  check_in_different_contexts(ord, f(g(x,y)) + 2 * f(x) - f(y), Incomp , f(g(x,y)) + 2 * f(x), p , f );
}

TEST_FUN(tricky_not_yet_implemented) {

  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Real)
  DECL_FUNC (f, {Real}, Real)
  DECL_FUNC (g, {Real, Real}, Real)
  DECL_PRED (p, {Real})
  DECL_CONST(a, Real)
  DECL_CONST(b, Real)
  DECL_CONST(c, Real)

  auto& ord = qkbo();


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

  auto& ord = qkbo();

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


  auto& ord = qkbo();

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

TEST_FUN(normal_form01) {
  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Real)
  mkAlascaSyntaxSugar(RealTraits{});
  DECL_CONST(a, Real)
  DECL_CONST(b, Real)
  // DECL_CONST(c, Real)
  DECL_FUNC (f, {Real}, Real)

  SIGNED_ATOM_TEST_FUNS
#define CHECK_EQ(is, exp) {                                                               \
    if (is != exp) {                                                                      \
      std::cout << "[ FAIL ] ";                                                           \
      std::cout << "[     case ] " << #is << std::endl;                                   \
      std::cout << "[       is ] " << is << std::endl;                                    \
      std::cout << "[ expected ] " << exp << std::endl;                                   \
      ASSERTION_VIOLATION                                                                 \
    } else {                                                                              \
      std::cout << "[  OK  ] " << #is << std::endl;                                       \
    }                                                                                     \
  };                                                                                      \

  CHECK_EQ(signedAtoms(2 * a() + b), 
      some(1, {
        SignedTerm::pos(a),
        SignedTerm::pos(a),
        SignedTerm::pos(b),
      }));

#if !ENABLE_ZERO_REMOVAL
  CHECK_EQ(signedAtoms(2 * a + 0 * b), 
      some(1, {
        SignedTerm::pos(a),
        SignedTerm::pos(a),
        SignedTerm::zero(b),
      }));
#endif // !ENABLE_ZERO_REMOVAL

  CHECK_EQ(signedAtoms(2 * a + 0 * a), 
      some(1, {
        SignedTerm::pos(a),
        SignedTerm::pos(a),
      }));

  CHECK_EQ(signedAtoms(2 * a + 1 * a), 
      some(1, {
        SignedTerm::pos(a),
        SignedTerm::pos(a),
        SignedTerm::pos(a),
      }));

  CHECK_EQ(signedAtoms(2 * a + -3 * a), 
      some(1, {
        SignedTerm::neg(a),
      }));

  CHECK_EQ(signedAtoms(2 * a + -4 * a), 
      some(1, {
        SignedTerm::neg(a),
        SignedTerm::neg(a),
      }));

  CHECK_EQ(signedAtoms(frac(1, 2) * a +  b), 
      some(2, {
        SignedTerm::pos(a),
        SignedTerm::pos(b),
        SignedTerm::pos(b),
      }));

  CHECK_EQ(signedAtoms(2 * a - a + -3 * a), 
      some(1, {
        SignedTerm::neg(a),
        SignedTerm::neg(a),
      }));

#if !ENABLE_ZERO_REMOVAL
  CHECK_EQ(signedAtoms(2 * a + a + -3 * a), 
      some(1, {
        SignedTerm::zero(a),
      }));

  CHECK_EQ(signedAtoms(-2 * a - a + 3 * a), 
      some(1, {
        SignedTerm::zero(a),
      }));
#endif // !ENABLE_ZERO_REMOVAL

  CHECK_EQ(signedAtoms(2 * f(a + 3 * b) - f(a - b + 4 * b)), 
      some(1, {
        SignedTerm::pos(f(a + 3 * b)),
      }));

#if !ENABLE_ZERO_REMOVAL
  CHECK_EQ(signedAtoms(f(3 * b) + f(0 * a - b + 4 * b)), 
      some(1, {
        SignedTerm::pos(f(3 * b)),
        SignedTerm::pos(f(0 * a + 3 * b)),
      }));
#endif // !ENABLE_ZERO_REMOVAL

#undef CHECK_EQ

  // Problem:
  //
  // -f(x) + f(y) > f(x)
  // but
  // -f(a) + f(a) < f(a)
  // since { 0 f(a) } < { +f(a) }

}

TEST_FUN(bug01) {

  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Real)
  DECL_CONST(a, Real)
  // DECL_CONST(b, Real)
  // DECL_CONST(c, Real)
  DECL_FUNC (f, {Real}, Real)
  auto& ord = qkbo();

  check(ord, f(f(a)) - f(f(a)) > 0, Less   , f(f(a)) > 0);
#if !ENABLE_ZERO_REMOVAL
  check(ord, f(f(a)) - f(f(a)) > 0, Greater, f(  a ) > 0);
  check(ord, f(f(a)) - f(f(a)) > 0, Incomp , f(  x ) > 0);
#endif // !ENABLE_ZERO_REMOVAL
}

TEST_FUN(bug02) {

  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Rat)
  mkAlascaSyntaxSugar(RatTraits{});
  DECL_CONST(a, Rat)
  DECL_FUNC (g, {Rat, Rat}, Rat)
  auto& ord = qkbo();

  check(ord, g(a,a), Incomp , frac(-1,2) * g(x,y));
}


TEST_FUN(numerals) {

  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Real)
#if !ENABLE_ZERO_REMOVAL
  DECL_CONST(a, Real)
#endif //!ENABLE_ZERO_REMOVAL
  auto& ord = qkbo();

  check(ord,  num(1), Equal, num(1));
  check(ord,  num(0), Equal, num(0));
  check(ord,  num(0) * 10, Equal, num(0));

  check(ord,  num(3), Greater, num(1));
  check(ord,  num(-3), Greater, num(1));
  check(ord,  num(-3), Greater, num(3));
  check(ord,  num(-3) + 2, Greater, num(3));
  check(ord,  num(3) + -2, Less, num(3));
#if !ENABLE_ZERO_REMOVAL
  check(ord,  num(3) + -2 + 0 * a, Greater, num(3));
#endif // !ENABLE_ZERO_REMOVAL
  check(ord,  num(2), Greater, num(1));
  {
    NUMBER_SUGAR(Rat)
    check(ord,  num(2), Greater, num(1));
  }
  {
    NUMBER_SUGAR(Int)
    check(ord,  num(2), Greater, num(1));
  }
  check(ord,  num(0), Less, num(1));
  check(ord,  num(1), Greater, num(0));

}


TEST_FUN(absEq) {

  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Real)
  DECL_CONST(a, Real)
  DECL_CONST(b, Real)
  // DECL_CONST(c, Real)
  DECL_FUNC (f, {Real}, Real)
  auto& ord = qkbo();

  check(ord,  f(a) - f(b) == 0, Greater, f(b) - f(a) == 0);
  check(ord, -f(a) - f(b) == 0, Greater, f(a) + f(b) == 0);

  check(ord,  f(a) + f(b) == 0, Greater   , f(a) - f(b) == 0);
  check(ord, -f(a) - f(b) == 0, Greater   , f(a) - f(b) == 0);
  check(ord,  f(a) + f(b) == 0, Greater   , f(b) - f(a) == 0);
  check(ord, -f(a) - f(b) == 0, Greater   , f(b) - f(a) == 0);

}

TEST_FUN(check_one_smallest) {

  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Real)


  TermList one = num(1);
  (void) one;
  DECL_CONST(a, Real)
  DECL_CONST(b, Real)
  DECL_CONST(c, Real)
  auto& ord = qkbo();

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
  auto& ord = qkbo();

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
    auto& ord = qkbo(/* rand */ true);

    check(ord, num(1), Less, a, /* silent */ true);
    check(ord, num(1), Less, b, /* silent */ true);
    check(ord, num(1), Less, c, /* silent */ true);
  }
}

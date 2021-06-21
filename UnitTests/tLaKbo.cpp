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
#include "Kernel/LaKbo.hpp"
#include "Kernel/KBO.hpp"
#include "Kernel/Ordering.hpp"
#include "Test/TestUtils.hpp"

//////////////////////////////////////////////////////////////////////////////// 
/////////////////////////////// HELPER FUNCTIONS /////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////// 

using namespace Test;
const LaKbo::Result Greater = LaKbo::Result::GREATER;
const LaKbo::Result Less    = LaKbo::Result::LESS;
const LaKbo::Result Equal   = LaKbo::Result::EQUAL;
const LaKbo::Result Incomp  = LaKbo::Result::INCOMPARABLE;

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

template<class SigTraits>
KboWeightMap<SigTraits> toWeightMap(unsigned introducedSymbolWeight, KboSpecialWeights<SigTraits> ws, const Map<unsigned, KboWeight>& xs, unsigned sz) 
{
  auto df = KboWeightMap<SigTraits>::dflt();
  df._specialWeights = ws;

  DArray<KboWeight> out(sz);
  for (unsigned i = 0; i < sz; i++) {
    auto w = xs.getPtr(i);
    out[i] = w == NULL ? df.symbolWeight(i) : *w;
  }
  return  {
    ._weights = out,
    ._introducedSymbolWeight = introducedSymbolWeight,
    ._specialWeights         = ws,
  };
}

template<class T>
void check__(Ordering& ord, T lhs, LaKbo::Result exp, T rhs) {
  // std::cout << std::endl;
  auto check_ = [&](T lhs, LaKbo::Result exp, T rhs) {
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

void check(LaKbo& ord, TermList lhs, LaKbo::Result exp, TermList rhs) 
{ check__(ord, lhs,exp,rhs); }

void check(LaKbo& ord, Literal* lhs, LaKbo::Result exp, Literal* rhs) 
{ check__(ord, lhs,exp,rhs); }

LaKbo laKbo(unsigned introducedSymbolWeight, 
    unsigned variableWeight, 
    const Map<unsigned, KboWeight>& funcs, 
    const Map<unsigned, KboWeight>& preds) {
  CALL("laKbo(...)")
 
  return LaKbo(KBO(toWeightMap<FuncSigTraits>(introducedSymbolWeight, { 
          ._variableWeight = variableWeight ,
          ._numInt  = variableWeight,
          ._numRat  = variableWeight,
          ._numReal = variableWeight,
        }, funcs, env.signature->functions()), 
#if __KBO__CUSTOM_PREDICATE_WEIGHTS__
             toWeightMap<PredSigTraits>(introducedSymbolWeight,
               KboSpecialWeights<PredSigTraits>::dflt(), 
               preds,
               env.signature->predicates()), 
#endif
             funcPrec(), 
             predPrec(), 
             PrecedenceOrdering::testLevels(),
             /*revereseLCM*/ false));
}


LaKbo laKbo(const Map<unsigned, KboWeight>& funcs, const Map<unsigned, KboWeight>& preds) {
  return laKbo(1, 1, funcs, preds);
}

void __weights(Map<unsigned, KboWeight>& ws) {
}

template<class A, class... As>
void __weights(Map<unsigned, KboWeight>& ws, pair<A, KboWeight> a, pair<As, KboWeight>... as) {
  ws.insert(get<0>(a).functor(), get<1>(a));
  __weights(ws, as...);
}

template<class... As>
Map<unsigned, KboWeight> weights(pair<As, KboWeight>... as) {
  Map<unsigned, KboWeight> out;
  __weights(out, as...);
  return out;
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////// TEST CASES //////////////////////////////////
//
// How to read the test cases in this file:
//
TEST_FUN(kbo_test01) {
  DECL_DEFAULT_VARS             // <- macro to initialize some syntax sugar for creating terms over a single uninterpreted sort
  DECL_SORT(srt)   // <- declares a function symbol with arity 1
  DECL_FUNC (f, {srt}, srt) // <- declares a function symbol with arity 1
  DECL_FUNC (g, {srt}, srt) // <- declares a function symbol with arity 1
  DECL_CONST(c, srt)    // <- declares a constant symbol
 
  // !!! The declaration order of function and constant symbols will define their precedence relation !!!

  auto ord = laKbo( 
      weights( // <- function symbol weights
        make_pair(f, 10u), // <- sets the weight of the function f to 10
        make_pair(c, 1u ) // <- sets the weight of the constant c to 1
        // other functions/constants default to weight 1
      ), 
      weights() // <- predicate symbol weights
      ); 

  check(ord, f(c), Greater, g(c));
}
//
//
//
////////////////////////////////////////////////////////////////////////////////

TEST_FUN(kbo_test02) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_FUNC (f, {srt}, srt)
  DECL_FUNC (g, {srt}, srt)
  DECL_CONST(c, srt)

  auto ord = laKbo(weights(make_pair(f, 10u)), weights());

  check(ord, f(c), Greater, g(g(g(g(g(c))))));
}

TEST_FUN(kbo_test03) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_FUNC (f, {srt}, srt)
  DECL_FUNC (g, {srt}, srt)
  DECL_CONST(c, srt)

  auto ord = laKbo(weights(make_pair(f, 10u)), weights());

  check(ord, f(x), Greater, g(g(g(g(g(c))))));
}

TEST_FUN(kbo_test04) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_FUNC (f, {srt}, srt)
  DECL_FUNC (g, {srt}, srt)

  auto ord = laKbo(weights(make_pair(f, 10u)), weights());

  check(ord, f(x), Incomp, g(g(g(g(g(y))))));
}

TEST_FUN(kbo_test05) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_FUNC (g, {srt}, srt)
  DECL_FUNC (f, {srt}, srt)

  auto ord = laKbo(weights(make_pair(f, 0u)), weights());

  check(ord, f(x), Less, g(x));
}

TEST_FUN(kbo_test06) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_FUNC(f, {srt}, srt)

  auto ord = laKbo(weights(make_pair(f, 0u)), weights());

  check(ord, f(x), Greater, x);
}

TEST_FUN(kbo_test07) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_FUNC(f, {srt}, srt)

  auto ord = laKbo(weights(make_pair(f, 0u)), weights());

  check(ord, f(x), Greater, x);
}

TEST_FUN(kbo_test08) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_FUNC(g, {srt}, srt)
  DECL_FUNC(f, {srt}, srt)

  auto ord = laKbo(weights(make_pair(f, 0u), make_pair(g, 1u)), weights());

  check(ord, g(f(x)), Less, f(g(x)));
}

TEST_FUN(kbo_test11) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_FUNC(g, {srt}, srt)
  DECL_FUNC(f, {srt}, srt)

  auto ord = laKbo(weights(make_pair(f, 0u), make_pair(g, 1u)), weights());

  check(ord, g(f(x)), Less, f(g(x)));
}

TEST_FUN(kbo_test12) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_CONST(b, srt)

  auto ord = laKbo(weights(), weights());

  check(ord, a, Less,b);
}

TEST_FUN(kbo_test13) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_CONST(b, srt)

  auto ord = laKbo(weights(make_pair(a,3u), make_pair(b,2u)), weights());

  check(ord, a, Greater,b);
}

TEST_FUN(kbo_test14) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_FUNC(f, {srt,srt}, srt)
  DECL_FUNC(g, {srt}, srt)
  DECL_FUNC(u, {srt}, srt)

  auto ord = laKbo(weights(make_pair(a,1u), make_pair(u,0u)), weights());

  check(ord, u(f(g(x),g(a))), Greater, u(f(x,g(a))));
}

TEST_FUN(kbo_test15) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_FUNC(f, {srt,srt}, srt)
  DECL_FUNC(g, {srt}, srt)
  DECL_FUNC(u, {srt}, srt)

  auto ord = laKbo(weights(make_pair(a,1u), make_pair(u,0u)), weights());

  check(ord, u(f(g(u(x)),g(a))), Greater, u(f(x,g(a))));
}

TEST_FUN(kbo_test16) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_FUNC(u, {srt}, srt)

  auto ord = laKbo(weights(make_pair(a,1u), make_pair(u,0u)), weights());

  check(ord, u(x), Greater, x);
}

TEST_FUN(kbo_test17) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_FUNC(f, {srt}, srt)
  DECL_FUNC(u, {srt}, srt)

  auto ord = laKbo(weights(make_pair(a,1u), make_pair(u,0u)), weights());

  check(ord, u(f(x)), Greater, f(x));
}

TEST_FUN(kbo_test18) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_FUNC(f, {srt}, srt)
  DECL_FUNC(u, {srt}, srt)

  auto ord = laKbo(weights(make_pair(a,1u), make_pair(u,0u)), weights());

  check(ord, f(u(x)), Greater, f(x));
}

TEST_FUN(kbo_test19) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_FUNC(f, {srt}, srt)
  DECL_FUNC(g, {srt}, srt)
  DECL_PRED(p, {srt})

  auto ord = laKbo(
      weights(
        make_pair(f,2u), 
        make_pair(g,3u)
      ), 
      weights(
        make_pair(p,2u)
      ));

  check(ord, p(f(g(x))), Less, p(g(f(x))));
}

TEST_FUN(kbo_test21) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_CONST(b, srt)

  auto ord = laKbo(
      10, // <- weight for introduced symbols
      10, // <- variable weight
      weights(
        make_pair(a,11u),
        make_pair(b,12u)
      ), 
      weights());

  check(ord, a, Less, b);
}


TEST_FUN(kbo_test22) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_PRED(r, {srt, srt})
  DECL_FUNC(g, {srt, srt}, srt)

  auto ord = laKbo(
      1, // <- weight for introduced symbols
      1, // <- variable weight
      weights(
        make_pair(r,1u)
      ), 
      weights());

  check(ord, r(x,y), Incomp, r(y,x));
  check(ord, g(x,y), Incomp, g(y,x));
}


// !!! There is no specific implementation for term-level ordering (atm), hence these tests are outdated
//
// TEST_FUN(lakbo_test01) {
//   DECL_DEFAULT_VARS
//   NUMBER_SUGAR(Int)
//   DECL_FUNC (f, {Int}, Int)
//   DECL_CONST(a, Int)
//
//   auto ord = laKbo(weights(
//       make_pair(f, 1u),
//       make_pair(a, 1u),
//       make_pair(add, 1u)
//     ), weights());
//
//   check(ord, x, Incomp, a); 
//
//   check(ord, f(x)    , Less, 3 * f(x));
//   check(ord, 5 * f(x), Greater, 3 * f(x));
//
//   check(ord,          f(x) , Less,     f(f(x)));
//   check(ord,      3 * f(x) , Less,     f(f(x)));
//   check(ord,          f(x) , Less, 3 * f(f(x)));
//   check(ord,      5 * f(x) , Less, 3 * f(f(x)));
//   check(ord, 7 * (5 * f(x)), Less, 3 * f(f(x)));
//   check(ord, 7 * (f(x) * 5), Less, 3 * f(f(x)));
//
//   check(ord, f(x) * f(x), Greater, f(x));
//
//   check(ord, f(a) + f(a), Less, a + f(f(a)));
//   check(ord, f(a) + f(a), Less, f(f(a)) + a);
//   check(ord, f(a) + x   , Incomp, a + f(x));
//   check(ord, f(a) + x   , Incomp, f(x) + a);
// }


TEST_FUN(lakbo_test02) {
  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Int)
  DECL_FUNC (f, {Int}, Int)
  DECL_CONST(a, Int)
  DECL_CONST(b, Int)

  auto ord = laKbo(weights(
      make_pair(f, 1u),
      make_pair(a, 1u),
      make_pair(b, 1u),
      make_pair(add, 1u)
    ), weights());

  check(ord,     f(x) > 0, Equal  , 3 * f(x) > 0); // <- are being normalized to the same thing
  check(ord, 5 * f(x) > 0, Equal  , 3 * f(x) > 0); // <- are being normalized to the same thing

  check(ord,     f(x) + a > 0, Less   , 3 * f(x) + a > 0);
  check(ord, 5 * f(x) + a > 0, Greater, 3 * f(x) + a > 0);

  check(ord,                     f(x) > 0, Less,     f(f(x)) > 0);
  check(ord,              f(x) + f(x) > 0, Less,     f(f(x)) > 0);
  check(ord,              f(a) + f(b) > 0, Less,     f(f(x)) > 0);
  check(ord,   3 * f(x) + f(a) + f(b) > 0, Less,     f(f(x)) > 0);
  check(ord,   3 * f(x) + x           > 0, Less,     f(f(x)) > 0);
  check(ord,   3 * f(x) + x     + y   > 0, Less,     f(f(x)) + y > 0);
  check(ord,   3 * f(x) + x     + y   > 0, Incomp,   f(f(x))     > 0);
}

// !!! There is no specific implementation for term-level ordering (atm), hence these tests are outdated
//
// TEST_FUN(lakbo_bug01) {
//   DECL_DEFAULT_VARS
//   DECL_VAR(x0, 0); DECL_VAR(x1, 1); DECL_VAR(x2, 2); DECL_VAR(x3, 3);
//   NUMBER_SUGAR(Int)
//   DECL_FUNC (f, {Int,Int}, Int)
//   DECL_CONST(a, Int)
//   DECL_CONST(b, Int)
//   DECL_CONST(c, Int)
//
//   // lG300($sum(f21,sLF0),f22)
//   // f($sum(a,b),c)
//   auto ord = laKbo(weights( make_pair(f, 1u)
//                           , make_pair(a, 1u)
//                           , make_pair(b, 1u)
//                           , make_pair(c, 1u)
//                           , make_pair(add, 1u)
//                           , make_pair(mul, 1u)
//                           )
//                 , weights());
//
//   check(ord, x, Incomp, a); 
//
//   check(ord, f(a + b, c), Equal , f(a + b, c));
//   check(ord, f(b + a, c), Incomp, f(a + b, c));
//
//   check(ord,  f(x0 * (x1 * x3), x0 * (x1 * x2)),
//         Less, f(x0 * (x1 * x2 + x1 * x3), x0 * (x1 * x2)) );
// }

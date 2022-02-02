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
#include "Kernel/KBO.hpp"
#include "Kernel/Ordering.hpp"

//////////////////////////////////////////////////////////////////////////////// 
/////////////////////////////// HELPER FUNCTIONS /////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////// 

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

DArray<int> predLevels() {
  DArray<int> out(env.signature->predicates());
  out.init(out.size(), 1);
  return out;
}
using namespace Kernel;

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

KBO kbo(unsigned introducedSymbolWeight, 
    unsigned variableWeight, 
    const Map<unsigned, KboWeight>& funcs, 
    const Map<unsigned, KboWeight>& preds) {
 
  return KBO(toWeightMap<FuncSigTraits>(introducedSymbolWeight, { 
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
             predLevels(),
             /*revereseLCM*/ false);
}


KBO kbo(const Map<unsigned, KboWeight>& funcs, const Map<unsigned, KboWeight>& preds) {
  return kbo(1, 1, funcs, preds);
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

  auto ord = kbo( 
      weights( // <- function symbol weights
        make_pair(f, 10u), // <- sets the weight of the function f to 10
        make_pair(c, 1u ) // <- sets the weight of the constant c to 1
        // other functions/constants default to weight 1
      ), 
      weights() // <- predicate symbol weights
      ); 

  ASS_EQ(ord.compare(f(c), g(c)), Ordering::Result::GREATER)
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

  auto ord = kbo(weights(make_pair(f, 10u)), weights());

  ASS_EQ(ord.compare(f(c), g(g(g(g(g(c)))))), Ordering::Result::GREATER)
}

TEST_FUN(kbo_test03) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_FUNC (f, {srt}, srt)
  DECL_FUNC (g, {srt}, srt)
  DECL_CONST(c, srt)

  auto ord = kbo(weights(make_pair(f, 10u)), weights());


  ASS_EQ(ord.compare(f(x), g(g(g(g(g(c)))))), Ordering::Result::GREATER)
}

TEST_FUN(kbo_test04) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_FUNC (f, {srt}, srt)
  DECL_FUNC (g, {srt}, srt)

  auto ord = kbo(weights(make_pair(f, 10u)), weights());

  ASS_EQ(ord.compare(f(x), g(g(g(g(g(y)))))), Ordering::Result::INCOMPARABLE)
}

TEST_FUN(kbo_test05) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_FUNC (g, {srt}, srt)
  DECL_FUNC (f, {srt}, srt)

  auto ord = kbo(weights(make_pair(f, 0u)), weights());

  ASS_EQ(ord.compare(f(x), g(x)), Ordering::Result::LESS)
}

TEST_FUN(kbo_test06) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_FUNC(f, {srt}, srt)

  auto ord = kbo(weights(make_pair(f, 0u)), weights());

  ASS_EQ(ord.compare(f(x), x), Ordering::Result::GREATER)
}

TEST_FUN(kbo_test07) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_FUNC(f, {srt}, srt)

  auto ord = kbo(weights(make_pair(f, 0u)), weights());

  ASS_EQ(ord.compare(f(x), x), Ordering::Result::GREATER)
}

TEST_FUN(kbo_test08) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_FUNC(g, {srt}, srt)
  DECL_FUNC(f, {srt}, srt)

  auto ord = kbo(weights(make_pair(f, 0u), make_pair(g, 1u)), weights());

  ASS_EQ(ord.compare(g(f(x)), f(g(x))), Ordering::Result::LESS)
}

TEST_FUN(kbo_test09) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_FUNC(f, {srt}, srt)
  DECL_FUNC(g, {srt}, srt)

  try {
    auto ord = kbo(weights(make_pair(g, 1u), make_pair(f, 0u)), weights());
    ASSERTION_VIOLATION
  } catch (UserErrorException&) {
    /* f is not maximal wrt precedence but has weight 0 */
  }
}


TEST_FUN(kbo_test10) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)

  try {
    auto ord = kbo(weights(make_pair(a, 0u)), weights());
    ASSERTION_VIOLATION
  } catch (UserErrorException&) {
    /* constant must be greater or equal to variable weight */
  }
}

TEST_FUN(kbo_test11) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_FUNC(g, {srt}, srt)
  DECL_FUNC(f, {srt}, srt)

  auto ord = kbo(weights(make_pair(f, 0u), make_pair(g, 1u)), weights());

  ASS_EQ(ord.compare(g(f(x)), f(g(x))), Ordering::Result::LESS)
}

TEST_FUN(kbo_test12) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_CONST(b, srt)

  auto ord = kbo(weights(), weights());

  ASS_EQ(ord.compare(a,b), Ordering::Result::LESS)
}

TEST_FUN(kbo_test13) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_CONST(b, srt)

  auto ord = kbo(weights(make_pair(a,3u), make_pair(b,2u)), weights());

  ASS_EQ(ord.compare(a,b), Ordering::Result::GREATER)
}

TEST_FUN(kbo_test14) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_FUNC(f, {srt,srt}, srt)
  DECL_FUNC(g, {srt}, srt)
  DECL_FUNC(u, {srt}, srt)

  auto ord = kbo(weights(make_pair(a,1u), make_pair(u,0u)), weights());

  ASS_EQ(ord.compare(u(f(g(x),g(a))), u(f(x,g(a)))), Ordering::Result::GREATER)
}

TEST_FUN(kbo_test15) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_FUNC(f, {srt,srt}, srt)
  DECL_FUNC(g, {srt}, srt)
  DECL_FUNC(u, {srt}, srt)

  auto ord = kbo(weights(make_pair(a,1u), make_pair(u,0u)), weights());

  ASS_EQ(ord.compare(u(f(g(u(x)),g(a))), u(f(x,g(a)))), Ordering::Result::GREATER)
}

TEST_FUN(kbo_test16) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_FUNC(u, {srt}, srt)

  auto ord = kbo(weights(make_pair(a,1u), make_pair(u,0u)), weights());

  ASS_EQ(ord.compare(u(x), x), Ordering::Result::GREATER)
}

TEST_FUN(kbo_test17) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_FUNC(f, {srt}, srt)
  DECL_FUNC(u, {srt}, srt)

  auto ord = kbo(weights(make_pair(a,1u), make_pair(u,0u)), weights());

  ASS_EQ(ord.compare(u(f(x)), f(x)), Ordering::Result::GREATER)
}

TEST_FUN(kbo_test18) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_FUNC(f, {srt}, srt)
  DECL_FUNC(u, {srt}, srt)

  auto ord = kbo(weights(make_pair(a,1u), make_pair(u,0u)), weights());

  ASS_EQ(ord.compare(f(u(x)), f(x)), Ordering::Result::GREATER)
}

TEST_FUN(kbo_test19) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_FUNC(f, {srt}, srt)
  DECL_FUNC(g, {srt}, srt)
  DECL_PRED(p, {srt})

  auto ord = kbo(
      weights(
        make_pair(f,2u), 
        make_pair(g,3u)
      ), 
      weights(
        make_pair(p,2u)
      ));

  ASS_EQ(ord.compare(p(f(g(x))), p(g(f(x)))), Ordering::Result::LESS)
}

TEST_FUN(kbo_test20) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)

  try {
    auto ord = kbo(
        10, // <- introduced symbol weight
        10, // <- variable weight
        weights(
          make_pair(a,1u)
        ), 
        weights());
    ASSERTION_VIOLATION
  } catch (UserErrorException&) {
    /* constants must have smaller or equal weight compared to variables */
  }
}

TEST_FUN(kbo_test21) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_CONST(b, srt)

  auto ord = kbo(
      10, // <- introduced symbol weight
      10, // <- variable weight
      weights(
        make_pair(a,11u),
        make_pair(b,12u)
      ), 
      weights());

  ASS_EQ(ord.compare(a, b), Ordering::Result::LESS)
}

TEST_FUN(kbo_test22) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)

  try {
    auto ord = kbo(
        9, // <- introduced symbol weight
        10, // <- variable weight
        weights(
          make_pair(a,12u)
        ), 
        weights());
    ASSERTION_VIOLATION
  } catch (UserErrorException&) {
    /* introduced symbol weight must be greater or equal to the variable weight */
  }
}



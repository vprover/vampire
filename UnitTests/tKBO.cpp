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
#include "Test/TestUtils.hpp"
#include "Kernel/KBO.hpp"
#include "Kernel/Ordering.hpp"

using namespace Test;

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

auto prty(TermList const& t) { return pretty(t); }
auto prty(Literal* const& t) { return pretty(t); }

#define _CHECK(ord, l, r, res)                                                                      \
  {                                                                                                 \
    auto cmp = ord.compare(l,r) ;                                                                   \
    if (cmp == res) {                                                                               \
      std::cout << "[  ok ] " << prty(l) << " " << cmp << " " << prty(r) << std::endl;              \
    } else {                                                                                        \
      std::cout << "[ fail ] " << prty(l) << " " << cmp << " " << prty(r) << std::endl;             \
      std::cout << "[  exp ] " << prty(l) << " " << res << " " << prty(r) << std::endl;             \
      exit(-1);                                                                                     \
    }                                                                                               \
  }                                                                                                 \

#define CHECK(ord, l, r, res)                                                                       \
  _CHECK(ord, l, r, res)                                                                            \
  _CHECK(ord, r, l, Ordering::reverse(res))                                                         \

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

  CHECK(ord, f(c), g(c), Ordering::Result::GREATER)
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

  CHECK(ord, f(c), g(g(g(g(g(c))))), Ordering::Result::GREATER)
}

TEST_FUN(kbo_test03) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_FUNC (f, {srt}, srt)
  DECL_FUNC (g, {srt}, srt)
  DECL_CONST(c, srt)

  auto ord = kbo(weights(make_pair(f, 10u)), weights());


  CHECK(ord, f(x), g(g(g(g(g(c))))), Ordering::Result::GREATER)
}

TEST_FUN(kbo_test04) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_FUNC (f, {srt}, srt)
  DECL_FUNC (g, {srt}, srt)

  auto ord = kbo(weights(make_pair(f, 10u)), weights());

  CHECK(ord, f(x), g(g(g(g(g(y))))), Ordering::Result::INCOMPARABLE)
}

TEST_FUN(kbo_test05) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_FUNC (g, {srt}, srt)
  DECL_FUNC (f, {srt}, srt)

  auto ord = kbo(weights(make_pair(f, 0u)), weights());

  CHECK(ord, f(x), g(x), Ordering::Result::LESS)
}

TEST_FUN(kbo_test06) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_FUNC(f, {srt}, srt)

  auto ord = kbo(weights(make_pair(f, 0u)), weights());

  CHECK(ord, f(x), x, Ordering::Result::GREATER)
}

TEST_FUN(kbo_test07) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_FUNC(f, {srt}, srt)

  auto ord = kbo(weights(make_pair(f, 0u)), weights());

  CHECK(ord, f(x), x, Ordering::Result::GREATER)
}

TEST_FUN(kbo_test08) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_FUNC(g, {srt}, srt)
  DECL_FUNC(f, {srt}, srt)

  auto ord = kbo(weights(make_pair(f, 0u), make_pair(g, 1u)), weights());

  CHECK(ord, g(f(x)), f(g(x)), Ordering::Result::LESS)
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

  CHECK(ord, g(f(x)), f(g(x)), Ordering::Result::LESS)
}

TEST_FUN(kbo_test12) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_CONST(b, srt)

  auto ord = kbo(weights(), weights());

  CHECK(ord, a,b, Ordering::Result::LESS)
}

TEST_FUN(kbo_test13) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_CONST(b, srt)

  auto ord = kbo(weights(make_pair(a,3u), make_pair(b,2u)), weights());

  CHECK(ord, a,b, Ordering::Result::GREATER)
}

TEST_FUN(kbo_test14) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_FUNC(f, {srt,srt}, srt)
  DECL_FUNC(g, {srt}, srt)
  DECL_FUNC(u, {srt}, srt)

  auto ord = kbo(weights(make_pair(a,1u), make_pair(u,0u)), weights());

  CHECK(ord, u(f(g(x),g(a))), u(f(x,g(a))), Ordering::Result::GREATER)
}

TEST_FUN(kbo_test15) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_FUNC(f, {srt,srt}, srt)
  DECL_FUNC(g, {srt}, srt)
  DECL_FUNC(u, {srt}, srt)

  auto ord = kbo(weights(make_pair(a,1u), make_pair(u,0u)), weights());

  CHECK(ord, u(f(g(u(x)),g(a))), u(f(x,g(a))), Ordering::Result::GREATER)
}

TEST_FUN(kbo_test16) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_FUNC(u, {srt}, srt)

  auto ord = kbo(weights(make_pair(a,1u), make_pair(u,0u)), weights());

  CHECK(ord, u(x), x, Ordering::Result::GREATER)
}

TEST_FUN(kbo_test17) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_FUNC(f, {srt}, srt)
  DECL_FUNC(u, {srt}, srt)

  auto ord = kbo(weights(make_pair(a,1u), make_pair(u,0u)), weights());

  CHECK(ord, u(f(x)), f(x), Ordering::Result::GREATER)
}

TEST_FUN(kbo_test18) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_FUNC(f, {srt}, srt)
  DECL_FUNC(u, {srt}, srt)

  auto ord = kbo(weights(make_pair(a,1u), make_pair(u,0u)), weights());

  CHECK(ord, f(u(x)), f(x), Ordering::Result::GREATER)
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

  CHECK(ord, p(f(g(x))), p(g(f(x))), Ordering::Result::LESS)
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

  CHECK(ord, a, b, Ordering::Result::LESS)
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


TEST_FUN(kbo_test23) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_CONST(b, srt)
  DECL_FUNC(f, {srt}, srt)
  DECL_FUNC(f2, {srt, srt}, srt)
  DECL_FUNC(f3, {srt, srt, srt}, srt)
  // DECL_FUNC(f4, {srt, srt, srt, srt}, srt)
  // DECL_FUNC(f5, {srt, srt, srt, srt, srt}, srt)
  // DECL_FUNC(f6, {srt, srt, srt, srt, srt, srt}, srt)

  auto ord = kbo(weights(), weights());

  CHECK(ord, x,a, Ordering::Result::GREATER_EQ)
  CHECK(ord, x,b, Ordering::Result::INCOMPARABLE)
  CHECK(ord, f(x),f(a), Ordering::Result::GREATER_EQ)
  CHECK(ord, f(x),f(b), Ordering::Result::INCOMPARABLE)
  CHECK(ord, f2(a, x),f(a, a), Ordering::Result::GREATER_EQ)
  CHECK(ord, f2(b, x),f(b, b), Ordering::Result::INCOMPARABLE)

  CHECK(ord, f2(a, x),f2(y, a), Ordering::Result::INCOMPARABLE)
  CHECK(ord, f2(a, x),f2(a, y), Ordering::Result::INCOMPARABLE)

  CHECK(ord, f3(a, x, a),f3(a, a, b), Ordering::Result::INCOMPARABLE)
  CHECK(ord, f3(a, a, a),f3(a, x, b), Ordering::Result::GREATER)
  CHECK(ord, f3(a, f(a), a),f3(a, f(x), b), Ordering::Result::GREATER)

}



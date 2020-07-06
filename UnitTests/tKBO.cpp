/**!  This file contains examples on how to use Test/SyntaxSugar.hpp.
 *
 * @autor Johannes Schoisswohl
 * @date 2020-04-29
 */

#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Kernel/KBO.hpp"
#include "Kernel/Ordering.hpp"

#define UNIT_ID KBO
UT_CREATE;

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

KBO kbo(const Map<unsigned, KBO::Weight>& funcs, const Map<unsigned, KBO::Weight>& preds) {
  auto toArray = [](const Map<unsigned, KBO::Weight>& xs, unsigned sz) -> DArray<KBO::Weight> {
    DArray<KBO::Weight> out(sz);
    for (int i = 0; i < sz; i++) {
      auto w = xs.getPtr(i);
      out[i] = w == NULL ? 1 : *w;
    }
    return out;
  };
  
  return KBO(toArray(funcs, env.signature->functions()), 
             toArray(preds, env.signature->predicates()), 
             funcPrec(), 
             predPrec(), 
             predLevels(),
             /*revereseLCM*/ false);
}



void __weights(Map<unsigned, KBO::Weight>& ws) {
}

template<class A, class... As>
void __weights(Map<unsigned, KBO::Weight>& ws, pair<A, KBO::Weight> a, pair<As, KBO::Weight>... as) {
  ws.insert(get<0>(a).functor(), get<1>(a));
  __weights(ws, as...);
}

template<class... As>
Map<unsigned, KBO::Weight> weights(pair<As, KBO::Weight>... as) {
  Map<unsigned, KBO::Weight> out;
  __weights(out, as...);
  return out;
}



TEST_FUN(kbo_test01) {
  FOF_SYNTAX_SUGAR
  FOF_SYNTAX_SUGAR_FUN  (f, 1)
  FOF_SYNTAX_SUGAR_FUN  (g, 1)
  FOF_SYNTAX_SUGAR_CONST(c)

  auto ord = kbo(weights(make_pair(f, 10u)), weights());

  ASS_EQ(ord.compare(f(c), g(c)), Ordering::Result::GREATER)
}


TEST_FUN(kbo_test02) {
  FOF_SYNTAX_SUGAR
  FOF_SYNTAX_SUGAR_FUN  (f, 1)
  FOF_SYNTAX_SUGAR_FUN  (g, 1)
  FOF_SYNTAX_SUGAR_CONST(c)

  auto ord = kbo(weights(make_pair(f, 10u)), weights());

  ASS_EQ(ord.compare(f(c), g(g(g(g(g(c)))))), Ordering::Result::GREATER)
}

TEST_FUN(kbo_test03) {
  FOF_SYNTAX_SUGAR
  FOF_SYNTAX_SUGAR_FUN  (f, 1)
  FOF_SYNTAX_SUGAR_FUN  (g, 1)
  FOF_SYNTAX_SUGAR_CONST(c)

  auto ord = kbo(weights(make_pair(f, 10u)), weights());

  ASS_EQ(ord.compare(f(x), g(g(g(g(g(c)))))), Ordering::Result::GREATER)
}

TEST_FUN(kbo_test04) {
  FOF_SYNTAX_SUGAR
  FOF_SYNTAX_SUGAR_FUN  (f, 1)
  FOF_SYNTAX_SUGAR_FUN  (g, 1)

  auto ord = kbo(weights(make_pair(f, 10u)), weights());

  ASS_EQ(ord.compare(f(x), g(g(g(g(g(y)))))), Ordering::Result::INCOMPARABLE)
}

TEST_FUN(kbo_test05) {
  FOF_SYNTAX_SUGAR
  FOF_SYNTAX_SUGAR_FUN  (f, 1)
  FOF_SYNTAX_SUGAR_FUN  (g, 1)

  auto ord = kbo(weights(make_pair(f, 0u)), weights());

  ASS_EQ(ord.compare(f(x), g(x)), Ordering::Result::LESS)
}

TEST_FUN(kbo_test06) {
  FOF_SYNTAX_SUGAR
  FOF_SYNTAX_SUGAR_FUN (f, 1)

  auto ord = kbo(weights(make_pair(f, 0u)), weights());

  ASS_EQ(ord.compare(f(x), x), Ordering::Result::GREATER)
}

TEST_FUN(kbo_test07) {
  FOF_SYNTAX_SUGAR
  FOF_SYNTAX_SUGAR_FUN (f, 1)

  auto ord = kbo(weights(make_pair(f, 0u)), weights());

  ASS_EQ(ord.compare(f(x), x), Ordering::Result::GREATER)
}

TEST_FUN(kbo_test08) {
  FOF_SYNTAX_SUGAR
  FOF_SYNTAX_SUGAR_FUN (f, 1)
  FOF_SYNTAX_SUGAR_FUN (g, 1)

  auto ord = kbo(weights(make_pair(f, 0u), make_pair(g, 1u)), weights());

  ASS_EQ(ord.compare(g(f(x)), f(g(x))), Ordering::Result::GREATER)
}

TEST_FUN(kbo_test09) {
  FOF_SYNTAX_SUGAR
  FOF_SYNTAX_SUGAR_FUN (g, 1)
  FOF_SYNTAX_SUGAR_FUN (f, 1)

  try {
    auto ord = kbo(weights(make_pair(g, 1u), make_pair(f, 0u)), weights());
    ASSERTION_VIOLATION
  } catch (UserErrorException e) {
    /* f is not minimal wrt precedence but has weight 0 */
  }
}


TEST_FUN(kbo_test10) {
  FOF_SYNTAX_SUGAR
  FOF_SYNTAX_SUGAR_CONST(a)

  try {
    auto ord = kbo(weights(make_pair(a, 0u)), weights());
    ASSERTION_VIOLATION
  } catch (UserErrorException e) {
    /* constant weights must be greater or equal to variable weight */
  }
}

TEST_FUN(kbo_test11) {
  FOF_SYNTAX_SUGAR
  FOF_SYNTAX_SUGAR_FUN (f, 1)
  FOF_SYNTAX_SUGAR_FUN (g, 1)

  auto ord = kbo(weights(make_pair(f, 0u), make_pair(g, 1u)), weights());

  ASS_EQ(ord.compare(g(f(x)), f(g(x))), Ordering::Result::GREATER)
}

TEST_FUN(kbo_test12) {
  FOF_SYNTAX_SUGAR
  FOF_SYNTAX_SUGAR_CONST(a)
  FOF_SYNTAX_SUGAR_CONST(b)

  auto ord = kbo(weights(), weights());

  ASS_EQ(ord.compare(a,b), Ordering::Result::LESS)
}

TEST_FUN(kbo_test13) {
  FOF_SYNTAX_SUGAR
  FOF_SYNTAX_SUGAR_CONST(a)
  FOF_SYNTAX_SUGAR_CONST(b)

  auto ord = kbo(weights(make_pair(a,3u), make_pair(b,2u)), weights());

  ASS_EQ(ord.compare(a,b), Ordering::Result::GREATER)
}

TEST_FUN(kbo_test14) {
  FOF_SYNTAX_SUGAR
  FOF_SYNTAX_SUGAR_FUN (u, 1)
  FOF_SYNTAX_SUGAR_CONST(a)
  FOF_SYNTAX_SUGAR_FUN (f, 2)
  FOF_SYNTAX_SUGAR_FUN (g, 1)

  auto ord = kbo(weights(make_pair(a,1u), make_pair(u,0u)), weights());

  ASS_EQ(ord.compare(f(g(x),g(a)), f(x,g(a))), Ordering::Result::GREATER)
}

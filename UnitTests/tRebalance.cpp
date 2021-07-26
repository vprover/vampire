/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Kernel/Rebalancing.hpp"
#include "Kernel/Rebalancing/Inverters.hpp"
#include "Indexing/TermSharing.hpp"
#include "Kernel/InterpretedLiteralEvaluator.hpp"
#include "Shell/TermAlgebra.hpp"


using namespace std;
using namespace Kernel;
using namespace Rebalancing;
using namespace Inverters;
using namespace Shell;

// TODO inline these macros
#define add(a,b) (a + b)
#define mul(a,b) (a * b)
#define minus(a) -(a)
#define lt(a,b) (a < b)
#define gt(a,b) (a > b)
#define leq(a,b) (a <= b)
#define geq(a,b) (a >= b)
#define neg(a)   ~(a)
#define eq(a,b)  (a == b)
#define neq(a,b) (a != b)

#define __expand__frac(...) { __VA_ARGS__ }
#define __expand__int(...)  { __VA_ARGS__ }
#define __expand__list(...) { __VA_ARGS__ }
#define bal(l,r) expected_t(l, TermSugar(r))

template<class Range, class Pred>
bool any(Range range, Pred p) {
  for (auto x : range) {
    if (p(x)) return true;
  }
  return false;
}

using expected_t = tuple<TermList, TermList>;

template<class ConstantType>
void test_rebalance(Literal* lit, initializer_list<expected_t> expected);

#define ToConstantType(type)  typename type##Traits::ConstantType

#define TEST_REBALANCE(name, type, equality, __list)                                                          \
    TEST_FUN(name ## _ ## type) {                                                                             \
      __ALLOW_UNUSED(                                                                                         \
        NUMBER_SUGAR(type)                                                                                    \
        DECL_DEFAULT_VARS                                                                                     \
        DECL_FUNC(f, {type}, type)                                                                            \
        DECL_CONST(a, type)                                                                                   \
        DECL_CONST(b, type)                                                                                   \
      )                                                                                                       \
      test_rebalance<ToConstantType(type)>((equality), __expand ## __list);                                   \
    }                                                                                                         \


/*
#define TEST_LIST(test_name, equality, __list)                                                                \
    TEST_FUN(test_name) {                                                                                     \
      NUMBER_SUGAR(Rat)                                                                                       \
      __ALLOW_UNUSED(                                                                                         \
        SYNTAX_SUGAR_SORT(list)                                                                               \
        SYNTAX_SUGAR_CONST(nil, list)                                                                         \
        SYNTAX_SUGAR_CONST(t, list)                                                                           \
        SYNTAX_SUGAR_FUN(cons,    list, __defaultSort, list)                                                  \
        SYNTAX_SUGAR_FUN(uncons1, __defaultSort      , list )                                                 \
        SYNTAX_SUGAR_FUN(uncons2, list                , list)                                                 \
        auto xL = Trm<UninterpretedTraits>(TermList::var(0));                                                 \
        auto yL = Trm<UninterpretedTraits>(TermList::var(1));                                                 \
        auto zL = Trm<UninterpretedTraits>(TermList::var(2));                                                 \
        env.signature->getFunction(nil .functor())->markTermAlgebraCons();                                    \
        env.signature->getFunction(cons.functor())->markTermAlgebraCons();                                    \
        env.signature->addTermAlgebra(new TermAlgebra(list.sortNumber(), {                                    \
            new TermAlgebraConstructor(nil.functor(),  {}),                                                   \
            new TermAlgebraConstructor(cons.functor(),  {uncons1.functor(), uncons2.functor()}),              \
          }));                                                                                                \
      )                                                                                                       \
      test_rebalance<ToConstantType(Rat)>((equality), __expand ## __list);                                    \
    }                                                                                                         \

#define TEST_ARRAY(test_name, equality, __list)                                                               \
    TEST_FUN(test_name) {                                                                                     \
      NUMBER_SUGAR(Rat)                                                                                       \
      __ALLOW_UNUSED(                                                                                         \
        SYNTAX_SUGAR_SORT(idxSrt)                                                                             \
        ARRAY_SYNTAX_SUGAR(array, idxSrt, __defaultSort)                                                      \
        SYNTAX_SUGAR_CONST(t, array)                                                                          \
        SYNTAX_SUGAR_CONST(u, array)                                                                          \
        SYNTAX_SUGAR_CONST(i, idxSrt)                                                                         \
      )                                                                                                       \
      test_rebalance<ToConstantType(Rat)>((equality), __expand ## __list);                                    \
    }                                                                                                         \
    */

#define TEST_REBALANCE_SPLIT(name, equality, __frac, __int)                                                   \
    TEST_REBALANCE(name, Real, equality, __frac)                                                              \
    TEST_REBALANCE(name, Rat , equality, __frac)                                                              \
    TEST_REBALANCE(name, Int , equality, __int)                                                               \


#define TEST_REBALANCE_ALL(name, equality, __list)                                                            \
    TEST_REBALANCE(name, Real, equality, __list)                                                              \
    TEST_REBALANCE(name, Rat , equality, __list)                                                              \
    TEST_REBALANCE(name, Int , equality, __list)                                                              \



TEST_REBALANCE_SPLIT(constants_1
    , eq(mul(2, x), 5)
    , __frac( 
        bal(x, frac(5,2)) 
    )
    , __int( ))

TEST_REBALANCE_SPLIT(constants_2,
    eq(mul(2, x), 4),
    __frac(
        bal(x, 2)
    ),
    __int())

TEST_REBALANCE_ALL(uninterpreted_1
    , eq(add(2, x), a)
    , __list(
        bal(x, add(a, -2))
    ))

TEST_REBALANCE_SPLIT(uninterpreted_2
    , eq(mul(x, 2), a)
    , __frac(
      bal(x, mul(a, frac(1, 2)))
    )
    , __int( ))

TEST_REBALANCE_SPLIT(multi_var_1
    , eq(mul(x, 2), mul(y, 2))
    , __frac(
        bal(x, y)
      , bal(y, x)
    )
    , __int( )
    )

TEST_REBALANCE_SPLIT(multi_var_2
    , eq(mul(x, 4), mul(y, 2))
    , __frac( 
        bal(y, mul(2,         x))
      , bal(x, mul(frac(1,2), y))
    )
    , __int( 
        // bal(y, mul(2, x))
    )
    )


TEST_REBALANCE_SPLIT(multi_var_3
    , eq(mul(x, 6), mul(y, 2))
    , __frac( 
        bal(y, mul(3,         x))
      , bal(x, mul(frac(1,3), y))
    )
    , __frac( 
        // bal(y, mul(3, x))
    )
    )


TEST_REBALANCE_SPLIT(multi_var_4
    , eq(mul(x, 2), y)
    , __frac(
        bal(x, mul(y, frac(1, 2)))
      , bal(y, mul(x , 2))
    )
    , __int( 
      bal(y, mul(x, 2))
    ))

TEST_REBALANCE_SPLIT(multi_var_5
    , eq(mul(x, 2), mul(y, 3))
    , __frac(
        bal(x, mul(frac(3, 2), y))
      , bal(y, mul(frac(2, 3), x))
    )
    , __int( ))


TEST_REBALANCE_ALL(rebalance_multiple_vars
    , eq(add(x, minus(y)), f(y))
    , __list(
        bal(x, add(f(y), y))
      , bal(y, minus(add(f(y), minus(x))))
    ))

TEST_REBALANCE_SPLIT(div_zero_1
    , eq(mul(x, 0), 7)
    , __int()
    , __frac()
    )

TEST_REBALANCE_SPLIT(div_zero_2
    , eq(mul(x, a), 7)
    , __int()
    , __frac()
    )

TEST_REBALANCE_SPLIT(div_zero_3
    , eq(mul(x, y), 7)
    , __int()
    , __frac()
    )

TEST_REBALANCE_SPLIT(div_zero_4
    , eq(mul(x, f(y)), 7)
    , __int()
    , __frac()
    )

TEST_REBALANCE_SPLIT(div_zero_5
    , eq(mul(0, x), 0)
    , __int()
    , __frac()
    )

TEST_REBALANCE_SPLIT(div_zero_6
    , eq(mul(2, x), 0)
    , __frac( 
          bal(x, 0)
      )
    , __int()
    )

TEST_REBALANCE_ALL(bug_1
    , neq(f(mul(16, z)), y)
    , __list(
      bal(y, f(mul(16, z)))
    ))

TEST_REBALANCE_SPLIT(bug_2
    , neq(add(x,mul(-1,x)), y)
    , __list(
        bal(y, add(x,mul(-1,x)))
      , bal(x, add(y, minus(mul(-1,x))))
      , bal(x, mul( add(y, minus(x)), -1))
    )
    , __list(
        bal(y, add(x,mul(-1,x)))
      , bal(x, add(y, minus(mul(-1,x))))
      , bal(x, mul(-1, add(y, minus(x))))
    ))

// UNSOUND
// /** 
//  * cons(x, y) = t
//  * ==> x = uncons1(t)
//  * ==> y = uncons2(t)
//  */
// TEST_LIST(rebalance_list_01
//     , neq(cons(x, yL), t)
//     , __list(
//         bal(yL, uncons2(t))
//       , bal(x , uncons1(t))
//     ))
//
// /** 
//  * cons(x + 1, y) = t
//  * ==> x = uncons1(t) - 1
//  * ==> y = uncons2(t)
//  */
// TEST_LIST(rebalance_list_02
//     , cons(x + 1, yL) != t
//     , __list(
//         bal(yL, uncons2(t))
//       , bal(x, uncons1(t) + (-1))
//     ))
//
// /** 
//  * store(t, i, x+1) = u
//  * ==> x = select(u, i) - 1
//  */
// TEST_ARRAY(rebalance_array_01
//     , store(t, i, x + 1) != u
//     , __list(
//         bal(x, select(u,i) + (-1))
//     ))


std::ostream& operator<<(std::ostream& out, initializer_list<expected_t> expected) {
  for (auto x : expected ) {
    out << "\t" << get<0>(x) << "\t->\t" << get<1>(x) << "\n";
  }
  return out;
}
template<class A>
std::ostream& operator<<(std::ostream& out, const BalanceIter<A>& x) {
  return out << "\t" << x.lhs() << "\t->\t" << x.buildRhs() << endl;
}
template<class A>
std::ostream& operator<<(std::ostream& out, const Balancer<A>& b) {
  for (auto x : b) {
    out << x;
  }
  return out;
}


template<class A>
void test_rebalance(Literal* lit_, initializer_list<expected_t> expected) {
  Literal& lit = *lit_;
  ASS(lit.isEquality());
  using balancer_t = Balancer<NumberTheoryInverter>;
  auto simplified = [](TermList t) -> TermList { 
    // DBG("simplifying ", t)
    static InterpretedLiteralEvaluator e = InterpretedLiteralEvaluator();
    if (t.isTerm()) {
      t = e.evaluate(t);
    }
    // DBG("end simplifying ", t)
    return t;
  };

  Stack<expected_t> results;
  unsigned cnt = 0;
  for (auto& bal : balancer_t(lit)) {

    auto lhs = bal.lhs();
    // auto rhs = bal.buildRhs();
    auto rhs = simplified(bal.buildRhs());

    results.push(expected_t(lhs, rhs));
    
    if (!any(expected, [&](const expected_t& ex) -> bool 
          { return get<0>(ex) == lhs && get<1>(ex) == rhs; }
      )) {

      cout << "case: " << lit << endl;
      cout << "unexpected entry in balancer:" << endl;
      cout << "\t"  << lhs << "\t->\t" << rhs << endl;
      cout << "expected: \n" << expected << endl;
      exit(-1);

    } 
    cnt++;
  }
  if (cnt != expected.size()) {
      cout << "case: " << lit << endl;
      cout << "unexpected results in balancer:" << endl;
      if (results.isEmpty()) {
        cout << "\t< nothing >" << endl;
      } else {
        for (auto r : results) {
          cout << "\t" << get<0>(r) << "\t->\t" << get<1>(r) << endl;
        }
      }
      cout << "expected: \n" << expected << endl;
      exit(-1);
  }
}



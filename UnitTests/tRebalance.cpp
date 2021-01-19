
  /*
   * File tRebalance.cpp.
   *
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
#include "Test/TestUtils.hpp"
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
using namespace Test;

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
      NUMBER_SUGAR(type)                                                                                      \
      DECL_DEFAULT_VARS                                                                                       \
      _Pragma("GCC diagnostic push")                                                                          \
      _Pragma("GCC diagnostic ignored \"-Wunused\"")                                                          \
        DECL_FUNC(f, {type}, type)                                                                            \
        DECL_CONST(a, type)                                                                                   \
        DECL_CONST(b, type)                                                                                   \
      _Pragma("GCC diagnostic pop")                                                                           \
      test_rebalance<ToConstantType(type)>((equality), __expand ## __list);                                   \
    }                                                                                                         \


/*
#define TEST_LIST(test_name, equality, __list)                                                                \
    TEST_FUN(test_name) {                                                                                     \
      NUMBER_SUGAR(Rat)                                                                                       \
      _Pragma("GCC diagnostic push")                                                                          \
      _Pragma("GCC diagnostic ignored \"-Wunused\"")                                                          \
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
      _Pragma("GCC diagnostic pop")                                                                           \
      test_rebalance<ToConstantType(Rat)>((equality), __expand ## __list);                                    \
    }                                                                                                         \

#define TEST_ARRAY(test_name, equality, __list)                                                               \
    TEST_FUN(test_name) {                                                                                     \
      NUMBER_SUGAR(Rat)                                                                                       \
      _Pragma("GCC diagnostic push")                                                                          \
      _Pragma("GCC diagnostic ignored \"-Wunused\"")                                                          \
        SYNTAX_SUGAR_SORT(idxSrt)                                                                             \
        ARRAY_SYNTAX_SUGAR(array, idxSrt, __defaultSort)                                                      \
        SYNTAX_SUGAR_CONST(t, array)                                                                          \
        SYNTAX_SUGAR_CONST(u, array)                                                                          \
        SYNTAX_SUGAR_CONST(i, idxSrt)                                                                         \
      _Pragma("GCC diagnostic pop")                                                                           \
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
    , 2 * x == 5
    , __frac( 
        bal(x, num(5) / 2) 
    )
    , __int( ))

TEST_REBALANCE_SPLIT(constants_2
    , 2 * x == 4
    , __frac(
        bal(x, num(4) / 2)
    )
    , __int())

TEST_REBALANCE_ALL(uninterpreted_1
    , 2 + x == a
    , __list(
        bal(x, a + -num(2))
    ))

TEST_REBALANCE_SPLIT(uninterpreted_2
    , x * 2 == a
    , __frac(
      bal(x, a / 2)
    )
    , __int( ))

TEST_REBALANCE_SPLIT(multi_var_1
    , x * 2 == y * 2
    , __frac(
        bal(x, (y * 2) / 2)
      , bal(y, (x * 2) / 2)
    )
    , __int( )
    )


TEST_REBALANCE_SPLIT(multi_var_2
    , x * 6 == y * 2
    , __frac( 
        bal(y,  (x * 6) / 2)
      , bal(x,  (y * 2) / 6)
    )
    , __frac( 
        // bal(y, mul(3, x))
    )
    )


TEST_REBALANCE_SPLIT(multi_var_3
    , x * 2 == y
    , __frac(
        bal(x, y / 2)
      , bal(y, x * 2)
    )
    , __int( 
      bal(y, x * 2)
    ))

TEST_REBALANCE_SPLIT(multi_var_4
    , x * 2 == y * 3
    , __frac(
        bal(x, (3 * y) / 2)
      , bal(y, (2 * x) / 3)
    )
    , __int( ))


TEST_REBALANCE_ALL(rebalance_multiple_vars
    , x + -y == f(y)
    , __list(
        bal(x,  (f(y) + -(-y)))
      , bal(y, -(f(y) + -x   ))
    ))

TEST_REBALANCE_SPLIT(div_zero_1
    , x * 0 == 7
    , __int()
    , __frac()
    )

TEST_REBALANCE_SPLIT(div_zero_2
    , x * a == 7
    , __int()
    , __frac()
    )

TEST_REBALANCE_SPLIT(div_zero_3
    , x * y == 7
    , __int()
    , __frac()
    )

TEST_REBALANCE_SPLIT(div_zero_4
    , x * f(y) == 7
    , __int()
    , __frac()
    )

TEST_REBALANCE_SPLIT(div_zero_5
    , 0 * x == 0
    , __int()
    , __frac()
    )

TEST_REBALANCE_SPLIT(div_zero_6
    , 2 * x == 0
    , __frac( 
          bal(x, 0 / num(2))
      )
    , __int()
    )

TEST_REBALANCE_ALL(bug_1
    , f(16 * z) != y
    , __list(
      bal(y, f(16 * z))
    ))

TEST_REBALANCE_SPLIT(bug_2
    , x + ( -1 * x ) != y
    , __list(
        bal(y, x +  (-1 * x))
      , bal(x, y + -(-1 * x))
      , bal(x, (y + -x) / -1)
    )
    , __list(
        bal(y, x +  (-1 * x))
      , bal(x, y + -(-1 * x))
      , bal(x, -1 * (y + -x))
    ))

// UNSOUND
// /** 
//  * cons(x, y) = t
//  * ==> x = uncons1(t)
//  * ==> y = uncons2(t)
//  */
// TEST_LIST(rebalance_list_01
//     , cons(x, yL) != t
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
    // static InterpretedLiteralEvaluator e = InterpretedLiteralEvaluator();
    // if (t.isTerm()) {
    //   t = e.evaluate(t);
    // }
    // DBG("end simplifying ", t)
    return t;
  };

  Stack<expected_t> results;
  unsigned cnt = 0;
  for (auto& bal : balancer_t(lit, NumberTheoryInverter( /* addGuards */ false))) {

    auto lhs = bal.lhs();
    // auto rhs = bal.buildRhs();
    auto inversionResult = bal.buildRhs();
    ASS(inversionResult.guards.isEmpty())
    auto rhs = simplified(inversionResult.term);

    results.push(expected_t(lhs, rhs));
    
    if (!any(expected, [&](const expected_t& ex) -> bool 
          { return TestUtils::eqModAC(get<0>(ex), lhs) &&  TestUtils::eqModAC(get<1>(ex), rhs); }
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



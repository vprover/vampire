


#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Kernel/Rebalancing.hpp"
#include "Kernel/Rebalancing/Inverters.hpp"
#include "Indexing/TermSharing.hpp"
#include "Kernel/InterpretedLiteralEvaluator.hpp"

#define UNIT_ID Rebalancing
UT_CREATE;
using namespace std;
using namespace Kernel;
using namespace Rebalancing;
using namespace Inverters;


#define __expand__frac(...) { __VA_ARGS__ }
#define __expand__int(...)  { __VA_ARGS__ }
#define __expand__list(...) { __VA_ARGS__ }
#define bal(l,r) expected_t(l, TermWrapper(r))

template<class Range, class Pred>
bool any(Range range, Pred p) {
  for (auto x : range) {
    if (p(x)) return true;
  }
  return false;
}

using expected_t = tuple<TermList, TermList>;

template<class ConstantType>
void test_rebalance(Literal& lit, initializer_list<expected_t> expected);

#define __TO_CONSTANT_TYPE_INT  IntegerConstantType
#define __TO_CONSTANT_TYPE_RAT  RationalConstantType
#define __TO_CONSTANT_TYPE_REAL RealConstantType
#define ToConstantType(type)  __TO_CONSTANT_TYPE_ ## type

#define TEST_REBALANCE(name, type, equality, __list) \
    TEST_FUN(name ## _ ## type) { \
      THEORY_SYNTAX_SUGAR(type) \
      _Pragma("GCC diagnostic push") \
      _Pragma("GCC diagnostic ignored \"-Wunused\"") \
        THEORY_SYNTAX_SUGAR_FUN(f, 1) \
      _Pragma("GCC diagnostic pop") \
      test_rebalance<ToConstantType(type)>((equality), __expand ## __list); \
    } \


#define TEST_REBALANCE_SPLIT(name, equality, __frac, __int) \
    TEST_REBALANCE(name, REAL, equality, __frac) \
    TEST_REBALANCE(name, RAT , equality, __frac) \
    TEST_REBALANCE(name, INT , equality, __int) \


#define TEST_REBALANCE_ALL(name, equality, __list) \
    TEST_REBALANCE(name, REAL, equality, __list) \
    TEST_REBALANCE(name, RAT , equality, __list) \
    TEST_REBALANCE(name, INT , equality, __list) \



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
void test_rebalance(Literal& lit, initializer_list<expected_t> expected) {
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



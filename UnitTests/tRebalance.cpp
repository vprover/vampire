


#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Kernel/Rebalancing.hpp"
#include "Indexing/TermSharing.hpp"

#define UNIT_ID Rebalancing
UT_CREATE;
using namespace std;
using namespace Kernel;
using namespace Rebalancing;


#define __expand__frac(...) { __VA_ARGS__ }
#define __expand__int(...)  { __VA_ARGS__ }
#define __expand__list(...) { __VA_ARGS__ }
#define bal(l,r) expected_t(l,r)

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

TEST_REBALANCE_ALL(constants_2,
    eq(mul(2, x), 4),
    __list(
        bal(x, 2)
    ))

TEST_REBALANCE_ALL(uninterpreted_1
    , eq(add(2, x), a)
    , __list(
        bal(x, add(-2, a))
    ))

TEST_REBALANCE_SPLIT(uninterpreted_2
    , eq(mul(x, 2), a)
    , __frac(
      bal(x, mul(frac(1, 2), a))
    )
    , __int( ))

TEST_REBALANCE_ALL(multi_var_1
    , eq(mul(x, 2), mul(y, 2))
    , __list(
        bal(x, y)
      , bal(y, x)
    ))

TEST_REBALANCE_ALL(multi_var_2
    , eq(mul(x, 4), mul(y, 2))
    , __list( 
        bal(y, mul(2, x))
    ))


TEST_REBALANCE_SPLIT(multi_var_3
    , eq(mul(x, 2), y)
    , __frac(
        bal(x, mul(frac(1, 2), y))
      , bal(y, mul(x, 2))
    )
    , __int( 
      bal(y, mul(x, 2))
    ))

TEST_REBALANCE_SPLIT(multi_var_4
    , eq(mul(x, 2), mul(y, 3))
    , __frac(
        bal(x, mul(frac(3, 2), y))
      , bal(y, mul(frac(2, 3), x))
    )
    , __int( ))


TEST_REBALANCE_ALL(rebalance_multiple_vars
    , eq(add(x, minus(y)), f(y))
    , __list(
        bal(x, add(y, f(y)))
      , bal(y, add(x, minus(f(y))))
    ))

std::ostream& operator<<(std::ostream& out, initializer_list<expected_t> expected) {
  for (auto x : expected ) {
    out << "\t" << get<0>(x) << "\t->\t" << get<1>(x) << "\n";
  }
  return out;
}
template<class A>
std::ostream& operator<<(std::ostream& out, const Balance<A>& x) {
  return out << "\t" << x.lhs() << "\t->\t" << x.buildRhs() << "\n";
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

  unsigned cnt = 0;
  for (auto b : Balancer<A>(lit)) {
    
    if (!any(expected, [&](const expected_t& ex) -> bool 
          { return get<0>(ex) == b.lhs() && get<1>(ex) == b.buildRhs(); }
      )) {
      cout << "unexpected entry in balancer: \n" << b << endl;
      cout << "expected: \n" << expected << endl;
      exit(-1);
    }

    cnt++;
  }
  if (cnt != expected.size()) {
      cout << "unexpected results in balancer: \n" << Balancer<A>(lit) << endl;
      cout << "expected: \n" << expected << endl;
  }
}



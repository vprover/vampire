#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Kernel/Rebalancing.hpp"
#include "Kernel/Rebalancing/Inverters.hpp"
#include "Indexing/TermSharing.hpp"
#include "Kernel/InterpretedLiteralEvaluator.hpp"
#include "Shell/TermAlgebra.hpp"

#define UNIT_ID Rebalancing
UT_CREATE;
using namespace std;
using namespace Shell;
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

// template<class ConstantType>
void test_rebalance(Literal& lit, initializer_list<expected_t> expected);

#define __TO_CONSTANT_TYPE_INT  IntegerConstantType
#define __TO_CONSTANT_TYPE_RAT  RationalConstantType
#define __TO_CONSTANT_TYPE_REAL RealConstantType
#define ToConstantType(type)  __TO_CONSTANT_TYPE_ ## type

#define TEST_LIST(test_name, equality, __list) \
    TEST_FUN(test_name) {            \
      THEORY_SYNTAX_SUGAR(RAT) \
      _Pragma("GCC diagnostic push") \
      _Pragma("GCC diagnostic ignored \"-Wunused\"") \
        SYNTAX_SUGAR_SORT(list) \
        SYNTAX_SUGAR_CONST(nil, list) \
        SYNTAX_SUGAR_CONST(t, list) \
        SYNTAX_SUGAR_FUN(cons,    2, {__default_sort, list}, list) \
        SYNTAX_SUGAR_FUN(uncons1, 1, {list      }, __default_sort) \
        SYNTAX_SUGAR_FUN(uncons2, 1, {list      }, list) \
        env.signature->getFunction(nil .functor())->markTermAlgebraCons(); \
        env.signature->getFunction(cons.functor())->markTermAlgebraCons(); \
        env.signature->addTermAlgebra(new TermAlgebra(list, { \
            new TermAlgebraConstructor(nil.functor(),  {}), \
            new TermAlgebraConstructor(cons.functor(),  {uncons1.functor(), uncons2.functor()}), \
          })); \
      _Pragma("GCC diagnostic pop") \
      test_rebalance((equality), __expand ## __list); \
    } \

#define TEST_ARRAY(test_name, equality, __list) \
    TEST_FUN(test_name) {            \
      THEORY_SYNTAX_SUGAR(RAT) \
      _Pragma("GCC diagnostic push") \
      _Pragma("GCC diagnostic ignored \"-Wunused\"") \
        SYNTAX_SUGAR_SORT(idxSrt) \
        ARRAY_SYNTAX_SUGAR(array, idxSrt, RAT) \
        SYNTAX_SUGAR_CONST(t, array) \
        SYNTAX_SUGAR_CONST(u, array) \
        SYNTAX_SUGAR_CONST(i, idxSrt) \
      _Pragma("GCC diagnostic pop") \
      test_rebalance((equality), __expand ## __list); \
    } \


#define TEST_REBALANCE(name, type, equality, __list) \
    TEST_FUN(name ## _ ## type) { \
      THEORY_SYNTAX_SUGAR(type) \
      _Pragma("GCC diagnostic push") \
      _Pragma("GCC diagnostic ignored \"-Wunused\"") \
        THEORY_SYNTAX_SUGAR_FUN(f, 1) \
      _Pragma("GCC diagnostic pop") \
      test_rebalance((equality), __expand ## __list); \
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
        bal(x, add(-2, a))
    ))

TEST_REBALANCE_SPLIT(uninterpreted_2
    , eq(mul(x, 2), a)
    , __frac(
      bal(x, mul(frac(1, 2), a))
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
        bal(x, mul(frac(1, 2), y))
      , bal(y, mul(2, x))
    )
    , __int( 
      bal(y, mul(2, x))
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


TEST_REBALANCE_ALL(bug_2
    , neq(add(x,mul(-1,x)), y)
    , __list(
        bal(y, add(x,mul(-1,x)))
      , bal(x, add(y, minus(mul(-1,x))))
      , bal(x, mul(-1, add(y, minus(x))))
    ))

/** 
 * cons(x, y) = t
 * ==> x = uncons1(t)
 * ==> y = uncons2(t)
 */
TEST_LIST(rebalance_list_01
    , neq(cons(x, y), t)
    , __list(
        bal(y, uncons2(t))
      , bal(x, uncons1(t))
    ))

/** 
 * cons(x + 1, y) = t
 * ==> x = uncons1(t) - 1
 * ==> y = uncons2(t)
 */
TEST_LIST(rebalance_list_02
    , neq(cons(add(x, 1), y), t)
    , __list(
        bal(y, uncons2(t))
      , bal(x, add(uncons1(t), -1))
    ))

/** 
 * store(t, i, x+1) = u
 * ==> x = select(u, i) - 1
 */
TEST_ARRAY(rebalance_array_01
    , neq(store(t, i, add(x, 1)), u)
    , __list(
        bal(x, add(select(u,i), -1))
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

template<class List, class Eq>
bool __permEq(const List& lhs, const List& rhs, Eq elemEq, DArray<unsigned>& perm, unsigned idx) {
  auto checkPerm = [&] (const List& lhs, const List& rhs, DArray<unsigned>& perm) {
    ASS_EQ(lhs.size(), perm.size());
    ASS_EQ(rhs.size(), perm.size());

    for (int i = 0; i < perm.size(); i++) {
      if (!elemEq(lhs[i], rhs[perm[i]])) return false;
    }
    return true;
  };
  if (checkPerm(lhs, rhs, perm)) {
    return true;
  }
  for (int i = idx; i < perm.size(); i++) {
    swap(perm[i], perm[idx]);

    
    if (__permEq(lhs,rhs, elemEq, perm, idx+1)) return true;

    swap(perm[i], perm[idx]);
  }

  return false;
}


template<class List, class Eq>
bool permEq(const List& lhs, const List& rhs, Eq elemEq) {
  ASS_EQ(lhs.size(), rhs.size());
  DArray<unsigned> perm(lhs.size());
  for (int i = 0; i < lhs.size(); i++) {
    perm[i] = i;
  }
  return __permEq(lhs, rhs, elemEq, perm, 0);
}

void __collect(unsigned functor, Term* t, Stack<TermList>& out) {
  ASS_EQ(t->functor(), functor);
  for (int i = 0; i < t->arity(); i++) {
    auto trm = t->nthArgument(i);
    if (trm->isVar()) {
      out.push(*trm);
    } else {
      ASS(trm->isTerm());
      if (trm->term()->functor() == functor) {
        __collect(functor, trm->term(), out);
      } else {
        out.push(*trm);
      }
    }
  }
}

Stack<TermList> collect(unsigned functor, Term* t) {
  Stack<TermList> out;
  __collect(functor, t, out);
  return out;
}



bool isAC(Theory::Interpretation i) {
  switch (i) {
#define NUM_CASE(oper) \
    case Kernel::Theory::INT_  ## oper: \
    case Kernel::Theory::REAL_ ## oper: \
    case Kernel::Theory::RAT_  ## oper

    NUM_CASE(PLUS):
    NUM_CASE(MULTIPLY):
      return true;
    default: 
      return false;
  }
}


bool eqModAC(TermList lhs, TermList rhs) {
  if (lhs.isVar() && rhs.isVar()) {
    return lhs.var() == rhs.var();
  } else if (lhs.isTerm() && rhs.isTerm()) {
    auto& l = *lhs.term();
    auto& r = *rhs.term();
    if ( l.functor() != r.functor() ) return false;
    auto fun = l.functor();
    if (theory->isInterpretedFunction(fun) && isAC(theory->interpretFunction(fun))) {
      Stack<TermList> lstack = collect(fun, &l);
      Stack<TermList> rstack = collect(fun, &r);
      return permEq(lstack, rstack, [](TermList l, TermList r) -> bool {
            return eqModAC(l, r);
      });
    } else {
      for (int i = 0; i < l.arity(); i++) {
        if (!eqModAC(*l.nthArgument(i), *r.nthArgument(i))) {
          return false;
        }
      }
      return true;
    }
  } else {
    return false;
  }
}


// template<class A>
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
  for (auto bal : balancer_t(lit)) {

    auto lhs = bal.lhs();
    // auto rhs = bal.buildRhs();
    auto rhs = simplified(bal.buildRhs());

    results.push(expected_t(lhs, rhs));
    
    if (!any(expected, [&](const expected_t& ex) -> bool 
          { return get<0>(ex) == lhs && eqModAC(get<1>(ex), rhs); }
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



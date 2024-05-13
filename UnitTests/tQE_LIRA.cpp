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

#include "Kernel/Theory.hpp"
#include <functional>
#include "Lib/VString.hpp"
#include "QE/ElimSet.hpp"
#include "Test/UnitTesting.hpp"
#include "Test/TestUtils.hpp"
#include "Test/SyntaxSugar.hpp"
#include "QE/LIRA.hpp"
#include "Kernel/LASCA.hpp"

using namespace QE;
using namespace Test;

#define VAR_X 0


RealConstantType simpl(RealConstantType t) 
{ return t; }

int simpl(int t) 
{ return t; }

TermList simpl(TermList t) 
{ return testLascaState()->normalize(t).denormalize(); }

ElimTerm simpl(ElimTerm t) 
{
  auto fin = t.asFinite();
  if (fin) {
    return ElimTerm(FiniteElimTerm(simpl(fin->term()), fin->epsilon(), fin->period()));
  } else {
    return t;
  }
}

template<class A>
Stack<A> simpl(Stack<A> const& t) 
{ return arrayIter(t).map([](auto& x){ return simpl(x); }).template collect<Stack>(); }

template<class A>
A simpl(Recycled<A> const& a) 
{ return simpl(*a); }

bool eqModAC(RealConstantType const& l, RealConstantType const& r)
{ return l == r; }

bool eqModAC(RealConstantType const& l, int r)
{ return l == RealConstantType(r); }

bool eqModAC(TermList l, TermList r)
{ return testLascaState()->equivalent(l,r); }

// template<class A>
// bool eqModAC(Stack<A> const& l_, Recycled<A> const& r_)
// {
//   TestUtils::eqModAC()
// }


bool eqModAC(ElimTerm const& l_, ElimTerm const& r_)
{ 
  // auto lhs = simpl(lhs_);
  // auto rhs = simpl(rhs_);
  // auto lhs = arrayIter(lhs_).map([](auto& x) -> ElimTerm { return x; }).template collect<Stack>().sorted().deduped();
  // auto rhs = arrayIter(rhs_).map([](auto& x) -> ElimTerm { return x; }).template collect<Stack>().sorted().deduped();
  // return TestUtils::permEq(lhs, rhs, [&](auto& l_, auto& r_) { 
    if (l_.isFinite() != r_.isFinite()) return false;
    else {
      auto& l = *l_.asFinite();
      auto& r = *r_.asFinite();
      return l.period() == r.period() 
          && l.epsilon() == r.epsilon() 
          && eqModAC(l.term(), r.term());
          // && TestUtils::eqModAC(l.term(), r.term());
    }
}
    //   }); }

template<class ElimSetish>
bool eqModAC(ElimSetish const& lhs_, ElimSetish const& rhs_)
{ 
  auto lhs = arrayIter(lhs_).map([](auto& x) -> ElimTerm { return x; }).template collect<Stack>().sorted().deduped();
  auto rhs = arrayIter(rhs_).map([](auto& x) -> ElimTerm { return x; }).template collect<Stack>().sorted().deduped();
  return TestUtils::permEq(lhs, rhs, [&](auto& l_, auto& r_) { 
    if (l_.isFinite() != r_.isFinite()) return false;
    else {
      auto& l = *l_.asFinite();
      auto& r = *r_.asFinite();
      return l.period() == r.period() 
          && l.epsilon() == r.epsilon() 
          && testLascaState()->equivalent(l.term(), r.term());
          // && TestUtils::eqModAC(l.term(), r.term());
    }
      }); }


template<class A>
bool eqModAC(Recycled<Stack<A>> const& l, Recycled<A> const& r)
{ return eqModAC(*l, r); }

struct AllContainted {
  Stack<ElimTerm> expected;

  Option<vstring> check(Stack<ElimTerm> const& result) {
    for (auto& s : arrayIter(expected)) {
      if (!arrayIter(result).any([&](auto& res) { return eqModAC(res, s); }) ) {
        return some(outputToString("not found: ", s));
      }
    }
    return {};
  }
  friend std::ostream& operator<<(std::ostream& out, AllContainted const& self)
  { return out << "contains: " << self.expected; }
};

struct ExpectedCheck : Coproduct<AllContainted> {
  using Coproduct::Coproduct;
  Option<vstring> check(Stack<ElimTerm> const& result) 
  { return apply([&](auto& x) { return x.check(result); }); }
  friend std::ostream& operator<<(std::ostream& out, ExpectedCheck const& self)
  { self.apply([&](auto& self) { out << self; }); return out; }
};

ElimTerm elimTerm(int i) { return ElimTerm(num(i)); }
ElimTerm elimTerm(ElimTerm e) { return ElimTerm(e); }
ElimTerm elimTerm(TermList t) { return ElimTerm(t); }
ElimSet elimSet() { return ElimSet(Stack<ElimTerm>()); }
template<class A, class... As> ElimSet elimSet(A a, As... as) { return ElimSet({elimTerm(a), elimTerm(as)...}); }


template<class... As>
ExpectedCheck containsAll(As... as) 
{ return ExpectedCheck(AllContainted{Stack<ElimTerm>{elimTerm(as)...}}); }


struct ElimSetTest {
  Stack<Literal*> conj;
  ExpectedCheck expected;

  void run() {
    auto result = LIRA::iterElimSet(VAR_X, conj).template collect<Stack>();
    auto simplResult = arrayIter(result)
          .map([](auto t) { return simpl(t); })
          .template collect<Stack>();
    auto error = expected.check(result);
    if (error.isSome()) {
        std::cout << "[         case ] " << pretty(     conj ) << std::endl;
        std::cout << "[       result ] " << pretty(      result ) << std::endl;
        std::cout << "[ simpl result ] " << pretty( simplResult ) << std::endl;
        std::cout << "[        error ] " << pretty(      *error ) << std::endl;
        std::cout << "[     expected ] " << pretty(    expected ) << std::endl;
        exit(-1);
    }
  }
};


struct CdvsTest {
  Stack<Literal*> formula;
  bool expected;

  void run() 
  {
    auto result = QE::CDVS::ConflictDrivenVirtualSubstitution::decide(formula);
    if (expected != result) {
      std::cout << "[         case ] " << pretty(     formula ) << std::endl;
      std::cout << "[       result ] " << pretty(      result ) << std::endl;
      std::cout << "[     expected ] " << pretty(    expected ) << std::endl;
      exit(-1);
    }
  }
};

struct TermSummaryTest {
  using TestFun = std::function<void(TermList, LiraTermSummary&)>;
  TermList term;
  Stack<TestFun> expected;

  void run() {
    auto result = LiraTermSummary::from(TermList::var(VAR_X), term);
    for (auto& c : expected) {
      c(term, result);
    }
  }
};



Period Z(int i)        { return Period(RealConstantType(i));    }
Period Z(int p, int q) { return Period(RealConstantType(p, q)); }

/* syntax sugar functions for writing nice test cases*/

inline ElimTerm operator+(int n, Epsilon e) { return num(n) + e; }
inline ElimTerm operator+(int n, Period  p) { return num(n) + p; }
ElimTerm minusInf() { return ElimTerm::minusInfinity(); }

constexpr Epsilon eps = Epsilon{};

#define SUGAR                                                                             \
  __ALLOW_UNUSED(                                                                         \
    NUMBER_SUGAR(Real)                                                                    \
    DECL_VAR(x, VAR_X)                                                                    \
    DECL_VAR(y, 1)                                                                        \
    DECL_VAR(z, 3)                                                                        \
    DECL_CONST(a, Real)                                                                   \
    DECL_CONST(b, Real)                                                                   \
    DECL_CONST(c, Real)                                                                   \
  )


#define RUN_TEST(name, ...)                                                               \
  TEST_FUN(name) { SUGAR; __VA_ARGS__.run(); }                                            \

#define TEST_EQ(lhs, rhs)                                                                 \
  [&](auto input, LiraTermSummary& result) {                                              \
    if (!(eqModAC(simpl(lhs), simpl(rhs)))) {                                             \
      std::cout << "[         case ] " << pretty(      input ) << std::endl;              \
      std::cout << "[       result ] " << pretty(     result ) << std::endl;              \
      std::cout << "[        check ] " << #lhs << " == " << pretty( rhs ) << std::endl;   \
      std::cout << "[       result ] " << pretty( simpl(lhs) ) << "\t (simplified)" << std::endl; \
      exit(-1);                                                                           \
    }                                                                                     \
  }                                                                                       \

template<class... Tests> 
auto allPass(Tests... ts) 
{ return Stack<TermSummaryTest::TestFun> { TermSummaryTest::TestFun(ts)... }; }

RUN_TEST(lra_01, 
    ElimSetTest {
      .conj = { x > 3 },
      .expected = containsAll( 3 + eps ),
    })

RUN_TEST(lra_02, 
    ElimSetTest {
      .conj = { x < 3 },
      .expected = containsAll( minusInf() ),
    })

RUN_TEST(lra_03, 
    ElimSetTest {
      .conj = { x >= 3 },
      .expected = containsAll( 3 ),
    })

RUN_TEST(lra_04, 
    ElimSetTest {
      .conj = { x <= 3 },
      .expected = containsAll( minusInf() ),
    })

RUN_TEST(lra_05, 
    ElimSetTest {
      .conj = { a < x, x < b },
      .expected = containsAll( minusInf(), a + eps ), 
    })

RUN_TEST(lra_06, 
    ElimSetTest {
      .conj = { a <= x, x < b },
      .expected = containsAll( a, minusInf() ), 
    })

RUN_TEST(lra_07, 
    ElimSetTest {
      .conj = { a <= x, x <= b },
      .expected = containsAll( a, minusInf() ), 
    })

RUN_TEST(floor_1, 
    ElimSetTest {
      .conj = { floor(x) == x },
      .expected = containsAll( 0 + Z(1) ), 
    })

RUN_TEST(floor_2, 
    ElimSetTest {
      .conj = { floor(x) >= x },
      .expected = containsAll( 0 + Z(1), num(0) + eps + Z(1) ),  // TODO do we really need eps and non-eps here
    })

RUN_TEST(floor_3, 
    ElimSetTest {
      .conj = { floor(x - frac(1,2)) == x },
      .expected = containsAll( frac(1,2) + Z(1) ), 
    })

RUN_TEST(floor_4, 
    ElimSetTest {
      .conj = { floor(x - a) == x },
      .expected = containsAll( a + Z(1) ), 
    })

RUN_TEST(floor_5, 
    ElimSetTest {
      .conj = { floor(x - a) == x },
      .expected = containsAll( a + Z(1) ), 
    })

RUN_TEST(motivating_test,
    ElimSetTest {
      .conj = { 
        floor( x ) - 1 >= 0
      // , x - 2 * floor(frac(1,2) * x) - b > 0
      // , floor(3 * x - c) + floor(-3 * x + c) == 0
      },
      .expected = containsAll( 1 ), 
    })

RUN_TEST(motivating_test_3,
    ElimSetTest {
      .conj = { 
        floor( x ) - 1 > 0
      // , x - 2 * floor(frac(1,2) * x) - b > 0
      // , floor(3 * x - c) + floor(-3 * x + c) == 0
      },
      .expected = containsAll( 2 ), 
    })

RUN_TEST(motivating_test_4,
    ElimSetTest {
      .conj = { 
        -floor( -x ) - 1 > 0
      // , x - 2 * floor(frac(1,2) * x) - b > 0
      // , floor(3 * x - c) + floor(-3 * x + c) == 0
      },
      .expected = containsAll( 1 + eps ), 
    })

RUN_TEST(motivating_test_5,
    ElimSetTest {
      .conj = { 
        -floor( -x ) - 1 == 0
      // , x - 2 * floor(frac(1,2) * x) - b > 0
      // , floor(3 * x - c) + floor(-3 * x + c) == 0
      },
      .expected = containsAll( 1 ), 
    })

RUN_TEST(motivating_test_2,
    ElimSetTest {
      .conj = { 
        floor( x ) - a >= 0
      // , x - 2 * floor(frac(1,2) * x) - b > 0
      // , floor(3 * x - c) + floor(-3 * x + c) == 0
      },
      .expected = containsAll( -floor(-a),  -floor(-a) + eps ), 
    })

 
  // - k: -1
  //   d: 1
  //   floors: 
  //   - { k: 1, l:  1, d: 0 }
  //   # - { k: 1, l: -1, d: 0 }
  //   color: blue
  //   relation: Geq
  //
  //
  // - k: 1
  //   d: 3
  //   floors: 
  //   color: red
  //   relation: Geq
  //
  //
  // - k: -2
  //   d: 3
  //   floors: 
  //   color: orange
  //   relation: Eq

template<class... As>
auto breakSet(As... as)
{ return Stack<ElimTerm> { as... }; }

RUN_TEST(some_props, 
    TermSummaryTest {
      .term = -floor(-3 * x + a) - x,
      .expected = allPass( TEST_EQ(result.linBounds.lower, -a)
                         , TEST_EQ(result.linBounds.delta, 1)
                         , TEST_EQ(result.lim,  floor(3 * x - a) + 1 - x)
                         , TEST_EQ(result.breaks,  breakSet( frac(1,3) * a + Z(1,3)))
                         , TEST_EQ(result.lowerX(), frac(1,2) * (a - 1)  )
                         , TEST_EQ(result.deltaX(), frac(1,2)  )
                         )
      // .expected = allPass(TEST_EQ(result.lim, -x + floor(x) + 1))
    })

RUN_TEST(some_props_2, 
    TermSummaryTest {
      .term = floor(2 * (-floor(-3 * x + a) - x) - b),
      .expected = allPass( 
                           TEST_EQ(result.breaks,  breakSet( frac(1,3) * a + Z(1,3)))
                         , TEST_EQ(result.per,     RealConstantType(1,3))
                         )
      // .expected = allPass(TEST_EQ(result.lim, -x + floor(x) + 1))
    })


RUN_TEST(motivating_props_1, 
    TermSummaryTest {
      .term = -x  - floor(-x),
      .expected = allPass(TEST_EQ(result.lim, -x + floor(x) + 1))
    })


RUN_TEST(motivating, 
    ElimSetTest {
      .conj = { 
         -x  - floor(-x) >= c
      ,  x >= floor(a) + frac(1,3)
      , -x >= floor(a) + frac(2,3)
      // , floor(3 * x - c) + floor(-3 * x + c) == 0
      },
      .expected = containsAll( a + Z(1) ), 
    })


// RUN_TEST(motivating, 
//     ElimSetTest {
//       .conj = { 
//          floor( x ) - a >= 0
//       ,  -x     >= 0
//       , x - 2 * floor(frac(1,2) * x) - 1 > 0
//       // , floor(3 * x - c) + floor(-3 * x + c) == 0
//       },
//       .expected = containsAll( a + Z(1) ), 
//     })

// RUN_TEST(motivating, 
//     ElimSetTest {
//       .conj = { 
//         floor( x ) - a >= 0
//       , x - 2 * floor(frac(1,2) * x) - b > 0
//       // , floor(3 * x - c) + floor(-3 * x + c) == 0
//       },
//       .expected = containsAll( a + Z(1) ), 
//     })

//////////////////////////////////////////////////////////////////////////////////////
// term property tests
//////////////////////////////////////////////////////////////////////////////////////

RUN_TEST(props_0,
    TermSummaryTest {
      .term     = floor( x ) - 1,
      .expected =  allPass(
            TEST_EQ(result.linBounds.lower, TermList(num(-2)))
          , TEST_EQ(result.lowerX(), TermList(num(1)))
          ),
    })

RUN_TEST(props_1,
    TermSummaryTest {
      .term     = TermList(num(1)),
      .expected =  allPass(
          TEST_EQ(result.linBounds.lower, TermList(num(1)))
          ),
    })

RUN_TEST(props_2,
    TermSummaryTest {
      .term     = TermList(-num(1)),
      .expected =  allPass(TEST_EQ(result.linBounds.lower, TermList(num(-1)))),
    })

RUN_TEST(props_3,
    TermSummaryTest {
      .term     = x,
      .expected =  allPass(
            TEST_EQ(result.linBounds.lower, TermList(num(0)))
          , TEST_EQ(result.lowerX(), TermList(num(0)))
          ),
    })

RUN_TEST(props_4,
    TermSummaryTest {
      .term     = floor(x),
      .expected =  allPass(
            TEST_EQ(result.linBounds.lower, TermList(num(-1)))
          , TEST_EQ(result.off, RealConstantType(1))
          , TEST_EQ(result.lowerX(), TermList(num(0)))
          ),
    })


RUN_TEST(props_5_a,
    TermSummaryTest {
      .term     = floor(x),
      .expected =  allPass(
            // TEST_EQ(result.linBounds.lower, TermList(num(-1)))
          // , TEST_EQ(result.off, RealConstantType(1))
            TEST_EQ(result.lowerX(), TermList(num(0)))
          , TEST_EQ(result.deltaX(), RealConstantType(1))
          ),
    })


RUN_TEST(props_5_b,
    TermSummaryTest {
      .term     = 2 * floor(x),
      .expected =  allPass(
            // TEST_EQ(result.linBounds.lower, TermList(num(-1)))
          // , TEST_EQ(result.off, RealConstantType(1))
            TEST_EQ(result.lowerX(), TermList(num(0)))
          , TEST_EQ(result.deltaX(), RealConstantType(1))
          ),
    })

RUN_TEST(props_5_c,
    TermSummaryTest {
      .term     = frac(1,2) * floor(x),
      .expected =  allPass(
            // TEST_EQ(result.linBounds.lower, TermList(num(-1)))
          // , TEST_EQ(result.off, RealConstantType(1))
            TEST_EQ(result.lowerX(), TermList(num(0)))
          , TEST_EQ(result.deltaX(), RealConstantType(1))
          ),
    })


//////////////////////////////////////////////////////////////////////////////////////
// Full Decisision procedure tests
//////////////////////////////////////////////////////////////////////////////////////


template<class T>
auto ceil(T t) 
{ return -floor(-t); }

RUN_TEST(lemma_ex00, // tryout
    CdvsTest {
      .formula  =  { 
        floor(y) - y + frac(1,2) > 0,
        x == 0,
        floor(2 * y) + 2 * y + frac(1,2) < x,
        // 0 < x, x < -1, // <-> false
      },
      .expected = true,
    })


RUN_TEST(lemma_ex01, // ebreak conflict
    CdvsTest {
      .formula  =  { 
        floor(y) - y == 0,
        0 < x, x < -1, // <-> false
      },
      .expected = false,
    })


RUN_TEST(lemma_ex02, // eseg conflict
    CdvsTest {
      .formula  =  { 
        floor(y) - y != 0,
        0 < x, x < -1, // <-> false
      },
      .expected = false,
    })


RUN_TEST(lemma_ex03, // einf conflict
    CdvsTest {
      .formula  =  { 
        floor(y) < 0,
        0 < x, x < -1, // <-> false
      },
      .expected = false,
    })


RUN_TEST(lemma_ex04, // epsilon lower bound conflict
    CdvsTest {
      .formula  =  { 
        frac(1,2) * y + 7 > 0,
        0 < x, x < -1, // <-> false
      },
      .expected = false,
    })

RUN_TEST(lemma_ex05, // lower bound conflict
    CdvsTest {
      .formula  =  { 
        frac(1,2) * y + 7 >= 0,
        0 < x, x < -1, // <-> false
      },
      .expected = false,
    })

RUN_TEST(lemma_ex06, // lower bound conflict
    CdvsTest {
      .formula  =  { 
        frac(1,2) * y + 7 < 0,
        0 < x, x < -1, // <-> false
      },
      .expected = false,
    })


RUN_TEST(decide_01,
    CdvsTest {
      // .formula  = exists(x, Real, floor(x - a) == x),
      .formula  =  { 
      floor(y) != y,
      2 * floor(x) - ceil(x) == 0,
      -floor(x) + 1 > 0
      // x >= 0 
      // ceil(y) - floor(y) - frac(1,2) >= 0 
      //              , x - floor(x) + y >= 0
                   },
        .expected = false,
    })

RUN_TEST(decide_02,
    CdvsTest {
      // .formula  = exists(x, Real, floor(x - a) == x),
      .formula  =  {floor(x - y) == x},
      .expected = true,
    })

RUN_TEST(decide_03,
    CdvsTest {
      // .formula  = exists(x, Real, floor(x - a) == x),
      .formula  =  { ceil(x) - floor(x) + frac(1,2) >= 0 
                   },
      .expected = true,
    })

RUN_TEST(decide_04,
    CdvsTest {
      // .formula  = exists(x, Real, floor(x - a) == x),
      .formula  =  { ceil(x) - floor(x) - frac(1,2) >= 0 
                   , x - floor(x) == 0
                   },
      .expected = false,
    })

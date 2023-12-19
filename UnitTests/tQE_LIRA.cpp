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


ElimTerm simpl(ElimTerm t) 
{
  auto fin = t.asFinite();
  if (fin) {
    return ElimTerm(FiniteElimTerm(testLascaState()->normalize(fin->term()).denormalize(), fin->epsilon(), fin->period()));
  } else {
    return t;
  }
}

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
          && testLascaState()->equivalent(l.term(), r.term());
          // && TestUtils::eqModAC(l.term(), r.term());
    }
}
    //   }); }

template<class ElimSetish1, class ElimSetish2>
bool eqModAC(ElimSetish1 const& lhs_, ElimSetish2 const& rhs_)
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
  Formula* formula;
  bool expected;

  void run() {
    auto result = QE::CDVS::ConflictDrivenVirtualSubstitution::decide(formula);
    // auto result = LIRA::iterElimSet(VAR_X, conj).template collect<Stack>();
    // auto simplResult = arrayIter(result)
    //       .map([](auto t) { return simpl(t); })
    //       .template collect<Stack>();
    // auto error = expected.check(result);
    if (expected != result) {
        std::cout << "[         case ] " << pretty(    *formula ) << std::endl;
        std::cout << "[       result ] " << pretty(      result ) << std::endl;
        std::cout << "[     expected ] " << pretty(    expected ) << std::endl;
        exit(-1);
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
    DECL_CONST(a, Real)                                                                   \
    DECL_CONST(b, Real)                                                                   \
    DECL_CONST(c, Real)                                                                   \
  )


#define RUN_TEST(name, ...)                                                               \
  TEST_FUN(name) { SUGAR; __VA_ARGS__.run(); }                                            \

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

//////////////////////////////////////////////////////////////////////////////////////
// Full Decisision procedure tests
//////////////////////////////////////////////////////////////////////////////////////

RUN_TEST(decide_01,
    CdvsTest {
      .formula  = exists(x, Real, floor(x - a) == x),
      .expected = true,
    })

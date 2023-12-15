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
#include "Test/UnitTesting.hpp"
#include "Test/TestUtils.hpp"
#include "Test/SyntaxSugar.hpp"
#include "QE/LIRA.hpp"

using namespace QE;
using namespace Test;

#define VAR_X 0

bool eqModAC(ElimSet const& lhs, ElimSet const& rhs)
{ return TestUtils::permEq(lhs, rhs, [&](auto& l_, auto& r_) { 
    if (l_.isFinite() != r_.isFinite()) return false;
    else {
      auto& l = *l_.asFinite();
      auto& r = *r_.asFinite();
      return l.period() == r.period() 
          && l.epsilon() == r.epsilon() 
          && TestUtils::eqModAC(l.term(), r.term());
    }
      }); }


struct ElimSetTest {
  Stack<Literal*> conj;
  Stack<ElimSet> expected;

  void run() {
    auto result = LIRA::computeElimSet(VAR_X, conj);
    for (auto& s : expected) {
      if (!arrayIter(result).any([&](auto& res) { return eqModAC(res, s); }) ) {
        std::cout << "[      case ] " << pretty(     conj ) << std::endl;
        std::cout << "[    result ] " << pretty(   result ) << std::endl;
        std::cout << "[ not found ] " << pretty(        s ) << std::endl;
        std::cout << "[  expected ] " << pretty( expected ) << std::endl;
        exit(-1);
      }
    }
  }
};

Period Z(int i)        { return Period(RealConstantType(i));    }
Period Z(int p, int q) { return Period(RealConstantType(p, q)); }

/* syntax sugar functions for writing nice test cases*/
ElimTerm elimTerm(int i) { return ElimTerm(num(i)); }
ElimTerm elimTerm(ElimTerm e) { return ElimTerm(e); }
ElimTerm elimTerm(TermList t) { return ElimTerm(t); }
ElimSet elimSet() { return ElimSet(Stack<ElimTerm>()); }
template<class A, class... As> ElimSet elimSet(A a, As... as) { return ElimSet({elimTerm(a), elimTerm(as)...}); }


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
      .expected = { elimSet(3 + eps) },
    })

RUN_TEST(lra_02, 
    ElimSetTest {
      .conj = { x < 3 },
      .expected = { elimSet(minusInf()) },
    })

RUN_TEST(lra_03, 
    ElimSetTest {
      .conj = { x >= 3 },
      .expected = { elimSet(3) },
    })

RUN_TEST(lra_04, 
    ElimSetTest {
      .conj = { x <= 3 },
      .expected = { elimSet(minusInf()) },
    })

RUN_TEST(lra_05, 
    ElimSetTest {
      .conj = { a < x, x < b },
      .expected = { elimSet(a + eps) }, 
    })

RUN_TEST(lra_06, 
    ElimSetTest {
      .conj = { a <= x, x < b },
      .expected = { elimSet(a, minusInf()) }, 
    })

RUN_TEST(lra_07, 
    ElimSetTest {
      .conj = { a <= x, x <= b },
      .expected = { elimSet(a, minusInf()) }, 
    })

RUN_TEST(floor_1, 
    ElimSetTest {
      .conj = { floor(x) == x },
      .expected = {elimSet(0 + Z(1)) }, 
    })

RUN_TEST(floor_2, 
    ElimSetTest {
      .conj = { floor(x) >= x },
      .expected = {elimSet(0 + Z(1)) }, 
    })

RUN_TEST(floor_3, 
    ElimSetTest {
      .conj = { floor(x - frac(1,2)) == x },
      .expected = {elimSet(frac(1,2) + Z(1)) }, 
    })

RUN_TEST(floor_4, 
    ElimSetTest {
      .conj = { floor(x - a) == x },
      .expected = {elimSet(a + Z(1)) }, 
    })

// RUN_TEST(floor_2, 
//     ElimSetTest {
//       .conj = { floor(x + a) == x },
//       .expected = { elimSet(-a) 
//                   , elimSet(0) }, 
//     })

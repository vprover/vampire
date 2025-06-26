/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Inferences/ALASCA/Demodulation.hpp"
#include "Inferences/ALASCA/Normalization.hpp"
#include "Test/SyntaxSugar.hpp"

#include "Test/SyntaxSugar.hpp"
#include "Test/FwdBwdSimplificationTester.hpp"
#include "Test/AlascaTestUtils.hpp"

// TODO rename FwdBwdSimplificationTester to SimplificationTester and SimplificationTester to  ImmediatesSimplificationTester

using namespace std;
using namespace Kernel;
using namespace Inferences;
using namespace Test;
using namespace Indexing;
using namespace Inferences::ALASCA;

#define SUGAR(Num)                                                                        \
  NUMBER_SUGAR(Num)                                                                       \
  DECL_DEFAULT_VARS                                                                       \
  DECL_CONST(a, Num)                                                                      \
  DECL_CONST(b, Num)                                                                      \
  DECL_CONST(c, Num)                                                                      \
  DECL_FUNC(f, {Num}, Num)                                                                \
  DECL_FUNC(f2, {Num}, Num)                                                                \
  DECL_FUNC(g, {Num, Num}, Num)                                                           \
  DECL_PRED(p, {Num})                                                                     \
  DECL_PRED(p0, {})                                                                       \
  DECL_PRED(r, {Num,Num})                                                                 \
  DECL_SORT(s)                                                                            \
  DECL_CONST(aU, s)                                                                       \
  DECL_CONST(bU, s)                                                                       \
  DECL_FUNC(fU, {s}, s)                                                                       \
  DECL_PRED(pU, {s})                                                                      \

#define MY_SYNTAX_SUGAR SUGAR(Rat) mkAlascaSyntaxSugar(Rat ## Traits{});

#define UWA_MODE Options::UnificationWithAbstraction::ALASCA_MAIN

template<class Rule, class... Args>
inline auto ALASCA_Demod_TestCase()  {
  auto state = testAlascaState();
  auto rule = move_to_heap(BinSimpl<Rule>(state));
  ALASCA::Normalization norm(state);
  return FwdBwdSimplification::TestCase()
    .fwd(rule)
    .bwd(rule)
    .fwdIdx({ rule->testToSimplIdx(), rule->testConditionIdx() })
    .bwdIdx({ rule->testToSimplIdx(), rule->testConditionIdx() })
    .normalize([norm = std::move(norm)](auto c) mutable { return norm.simplify(c); });
}

auto ALASCA_Demod_TestCase_SuperpositionDemodConf(bool preordered)  {

  auto val = preordered ? Options::Demodulation::PREORDERED : Options::Demodulation::ALL;
  env.options->alascaDemodulationFwd(val);
  env.options->alascaDemodulationBwd(val);
  return ALASCA_Demod_TestCase<SuperpositionDemodConf>();
}

#define TEST_SIMPLIFICATION_SuperpositionDemodConf_both(testname, ...)              \
                                                                                          \
  TEST_SIMPLIFICATION(testname,                                                           \
      ALASCA_Demod_TestCase_SuperpositionDemodConf(/* preordered */ false)               \
        __VA_ARGS__                                                                       \
      )                                                                                   \
                                                                                          \
  TEST_SIMPLIFICATION(testname ## _preordered,                                             \
      ALASCA_Demod_TestCase_SuperpositionDemodConf(/* preordered */ true)                \
        __VA_ARGS__                                                                       \
      )                                                                                   \

#define TEST_SIMPLIFICATION_SuperpositionDemodConf_preorderedNotApplicable(testname, ...)              \
                                                                                          \
  TEST_SIMPLIFICATION(testname,                                                           \
      ALASCA_Demod_TestCase_SuperpositionDemodConf(/* preordered */ false)               \
        __VA_ARGS__                                                                       \
      )                                                                                   \
                                                                                          \
  TEST_SIMPLIFICATION(testname ## _preordered,                                             \
      ALASCA_Demod_TestCase_SuperpositionDemodConf(/* preordered */ true)                \
        __VA_ARGS__                                                                       \
        .expectNotApplicable() \
      )                                                                                   \

/////////////////////////////////
// superposition demod tests
/////////////////////////////////


TEST_SIMPLIFICATION_SuperpositionDemodConf_both(basic01,
      .simplifyWith({    clause(   { 0 == f(a) - a  }   ) })
      .toSimplify  ({    clause(   { p(f(a))        }   ) })
      .expected(    {    clause(   { p(  a )        }   ) })
    )

TEST_SIMPLIFICATION_SuperpositionDemodConf_both(basic01b,
      .simplifyWith({    clause(   { 0 == -f(a) + a  }   ) })
      .toSimplify  ({    clause(   { p(f(a))         }   ) })
      .expected(    {    clause(   { p(  a )         }   ) })
    )


TEST_SIMPLIFICATION_SuperpositionDemodConf_both(basic02,
      .simplifyWith({    clause(   { 0 == f(a) - a   }   )
                    ,    clause(   { 0 == g(b,a) - b }   ) })
      .toSimplify  ({    clause(   { r(f(a), f(b))   }   ) })
      .expected(    {    clause(   { r(  a , f(b))   }   ) })
      .justifications({  clause(   {  0 == f(a) - a  }   ) })
    )

TEST_SIMPLIFICATION_SuperpositionDemodConf_both(basic03,
      .simplifyWith({    clause(   { 0 == f(x) - x      }   ) })
      .toSimplify  ({    clause(   { r(f(a), f(b))      }   ) })
      .expected(    {    clause(   { r(f(a),   b )      }   ) })
    )

TEST_SIMPLIFICATION_SuperpositionDemodConf_both(basic04,
      .simplifyWith({    clause(   { 0 == f(x) - x }   ) })
      .toSimplify  ({    clause(   { p(f(a))       }   ) , clause(   { p(f(b)) }   ) })
      .expected(    {    clause(   { p(  a )       }   ) , clause(   { p(  b ) }   ) })
    )

TEST_SIMPLIFICATION_SuperpositionDemodConf_both(basic05,
      .simplifyWith({    clause(   { 0 == f(a) - a }   ), clause(   { 0 == f(b) - b }   ) })
      .toSimplify  ({    clause(   { p(f(a)) }         ), clause(   { p(f(b)) }         ) })
      .expected(    {    clause(   { p(  a ) }         ), clause(   { p(  b ) }         ) })
    )

TEST_SIMPLIFICATION_SuperpositionDemodConf_both(basic06,
      .simplifyWith({    clause(   { 0 == f(a) - a }   ), clause(   { 0 == f(b) - b }   ) })
      .toSimplify  ({    clause(   { p(f(a)) }         ), clause(   { p(f(f(a))) }         ) })
      .expected(    {    clause(   { p(  a ) }         ), clause(   { p(  f(a) ) }         ) })
      .justifications({  clause(   {  0 == f(a) - a  }   ) })
    )

TEST_SIMPLIFICATION_SuperpositionDemodConf_both(basic07,
      .simplifyWith({    clause(   { 0 == g(a, x) - x      }   ) })
      .toSimplify  ({    clause(   { p(g(a,b))             }   ) })
      .expected(    {    clause(   { p(    b )             }   ) })
    )

TEST_SIMPLIFICATION_SuperpositionDemodConf_both(basic08,
      .simplifyWith({    clause(   { 0 == g(a, x) - x      }   ) })
      .toSimplify  ({    clause(   { p(g(y,b))             }   ) })
      .expectNotApplicable()
    )

TEST_SIMPLIFICATION_SuperpositionDemodConf_both(basic09,
      .simplifyWith({    clause(   { 0 == frac(1,3) * f(g(a,a)) - a  }   ) })
      .toSimplify  ({    clause(   { p( f(g(a,a)))                   }   ) })
      .expected(    {    clause(   { p(3 * a)                        }   ) })
    )
TEST_SIMPLIFICATION(basic10,
    ALASCA_Demod_TestCase_SuperpositionDemodConf(/* preordered */ false)
      .simplifyWith({    clause(   { 0 == -2 * f(x) + a }   ) })
      .toSimplify  ({    clause(   { p(f(b)) }   ) })
      .expected    ({    clause(   { p(frac(1,2) * a) }   ) })
    )

// checking `C[sσ] ≻ (±ks + t ≈ 0)σ`
TEST_SIMPLIFICATION_SuperpositionDemodConf_both(ordering01,
      .simplifyWith({    clause(   { 0 == f(x) + g(x,x) }   ) })
      .toSimplify  ({    clause(   { 0 == g(a,a)    }   ) })
      .expectNotApplicable()
    )

// checking `sσ ≻ terms(t)σ`
TEST_SIMPLIFICATION_SuperpositionDemodConf_both(ordering02,
      .simplifyWith({    clause(   { 0 == f(x) + g(y,y) }       ) })
      .toSimplify  ({    clause(   { 0 == g(a,a) + f(x) + a }   ) })
      .expectNotApplicable()
    )

// checking `sσ ≻ terms(t)σ`
TEST_SIMPLIFICATION_SuperpositionDemodConf_both(sum01,
      .simplifyWith({    clause(   { 0 == x + g(x,x) + a }       ) })
      .toSimplify  ({    clause(   { p(g(f(f(a)),f(f(a))))  }   ) })
      .expected(    {    clause(   { p(    - a - f(f(a)) )  }   ) })
    )

TEST_SIMPLIFICATION_SuperpositionDemodConf_both(sum02,
      .simplifyWith({    clause(   { 0 == x + g(x,x) }       ) })
      .toSimplify  ({    clause(   { p(g(f(f(a)),f(f(a))))  }   ) })
      .expected(    {    clause(   { p(    - f(f(a))     )  }   ) })
    )

TEST_SIMPLIFICATION_SuperpositionDemodConf_both(sum03,
      .simplifyWith({    clause(   { 0 == a + g(x,x) }       ) })
      .toSimplify  ({    clause(   { p(g(f(f(a)),f(f(a))))  }   ) })
      .expected(    {    clause(   { p(    - a           )  }   ) })
    )

TEST_SIMPLIFICATION_SuperpositionDemodConf_both(sum_of_vars_01,
      .simplifyWith({    clause(   { 0 == x - y + g(x,y) }       ) })
      .toSimplify  ({    clause(   { p(g(x, y))  }   ) })
      .expected(    {    clause(   { p(y - x)  }   ) })
    )

TEST_SIMPLIFICATION_SuperpositionDemodConf_both(bug01,
      .simplifyWith({    clause(   { 0 == g(x, y) - y  }   ) })
      .toSimplify  ({    clause(   { p(g(z,a))         }   ) })
      .expected(    {    clause(   { p(    a )         }   ) })
    )

TEST_SIMPLIFICATION_SuperpositionDemodConf_both(misc01,
      .simplifyWith({    clause(   { 0 == a  }   ) })
      .toSimplify  ({    clause(   { ~p0(), a == b }   ) })
      .expected(    {    clause(   { ~p0(), b == 0 }   ) })
    )

TEST_SIMPLIFICATION_SuperpositionDemodConf_both(misc02,
      .simplifyWith({    clause(   { 0 == b  }   ) })
      .toSimplify  ({    clause(   { ~p0(), a == b }   ) })
      .expected(    {    clause(   { ~p0(), a == 0 }   ) })
    )

TEST_SIMPLIFICATION_SuperpositionDemodConf_preorderedNotApplicable(bug02,
      .simplifyWith({    clause(   { x == aU  }   ) })
      .toSimplify  ({    clause(   { pU(bU) }   ) })
      .expected(    {    clause(   { pU(aU) }   ) })
    )

TEST_SIMPLIFICATION_SuperpositionDemodConf_preorderedNotApplicable(preordered_check_01,
      .simplifyWith({    clause(   { g(x, y) == g(y, x)   }   ) })
      .toSimplify  ({    clause(   { p(g(b, a)) }   ) })
      .expected(    {    clause(   { p(g(a, b)) }   ) })
    )

// checking `sσ ≻ tσ` being aware of variable banks. can lead to invalid terms
TEST_SIMPLIFICATION_SuperpositionDemodConf_both(bug03,
      .simplifyWith({    clause(   { f(x) == y  }   ) })
      .toSimplify  ({    clause(   { f(y) != 0 }   ) })
      .expectNotApplicable()
    )

//   ;- unit id: 296
// (assert (forall ((x0 Real))(or false
//   (> (* (-(/ 1.0 1.0)) (ff (skx x0))) (/ 0.0 1.0))
//   (>= (+ delta (* (/ 2.0 1.0) (skx x0))) (/ 0.0 1.0))
//   (>= (skx x0) (/ 0.0 1.0))
//   )))
//
// ;- unit id: 746
// (assert (forall ((x0 Real))(or false
//   (= (/ 0.0 1.0) (+ delta (* (-(/ 2.0 1.0)) (skx x0))))
//   )))
//
//
// ;- rule: alasca superposition demodulation
//
// ;- unit id: 767
// (assert (not (or false
//   (> (* (-(/ 1.0 1.0)) (ff (* 1.0 delta))) (/ 0.0 1.0))
//   (>= (+ delta (* (/ 2.0 1.0) (* 1.0 delta))) (/ 0.0 1.0))
//   (>= (* 1.0 delta) (/ 0.0 1.0))
//   )))
// (check-sat)
TEST_SIMPLIFICATION_SuperpositionDemodConf_both(bug04,
      //   (= (/ 0.0 1.0) (+ delta (* (-(/ 2.0 1.0)) (skx x0))))
      .simplifyWith({    clause(   { 0 == -2 * f(x) + a }   ) })
      .toSimplify  ({    clause(   {
        //   (> (* (-(/ 1.0 1.0)) (ff (skx x0))) (/ 0.0 1.0))
        -1 * f2(f(x)) > 0,
        //   (>= (+ delta (* (/ 2.0 1.0) (skx x0))) (/ 0.0 1.0))
        a + -2 * f(x) >= 0,
        //   (>= (skx x0) (/ 0.0 1.0))
        f(x) >= 0
          }   ) })
      .expected    ({    clause(   { 
        -1 * f2(frac(1,2) * a) > 0,
        a + -2 * (frac(1,2) * a) >= 0,
        frac(1,2) * a >= 0
          }   ) })
    )

/////////////////////////////////
// coherence demod tests
/////////////////////////////////

TEST_SIMPLIFICATION(demod_basic_01,
    ALASCA_Demod_TestCase<CoherenceDemodConf<RatTraits>>()
      .simplifyWith({    clause(   { isInt(f(x))  }   ) })
      .toSimplify  ({    clause(   { p(floor(f(a))) }   ) })
      .expected(    {    clause(   { p(f(a)) }   ) })
    )


TEST_SIMPLIFICATION(demod_basic_02,
    ALASCA_Demod_TestCase<CoherenceDemodConf<RatTraits>>()
      .simplifyWith({    clause(   { isInt(f(x))  }   ) })
      .toSimplify  ({    clause(   { floor(f(a)) != a }   ) })
      .expected(    {    clause(   { f(a) != a }   ) })
    )


// checking `C[sσ] ≻ isInt(s + t)σ`
TEST_SIMPLIFICATION(demod_basic_03,
    ALASCA_Demod_TestCase<CoherenceDemodConf<RatTraits>>()
      .simplifyWith({    clause(   { isInt(f(x))  }   ) })
      .toSimplify  ({    clause(   { floor(f(a)) == a }   ) })
      .expectNotApplicable()
    )

TEST_SIMPLIFICATION(demod_basic_04,
    ALASCA_Demod_TestCase<CoherenceDemodConf<RatTraits>>()
      .simplifyWith({    clause(   { isInt(f(a))  }   ) })
      .toSimplify  ({    clause(   { floor(f(x)) != x }   ) })
      .expectNotApplicable()
    )

// checking `sσ ≻ uσ`
TEST_SIMPLIFICATION(demod_basic_05,
    ALASCA_Demod_TestCase<CoherenceDemodConf<RatTraits>>()
      .simplifyWith({    clause(   { isInt(f(x) + x)  }   ) })
      .toSimplify  ({    clause(   { p(floor(f(a) + a)) }   ) })
      .expected    ({    clause(   { p(      f(a) + a ) }   ) })
    )

// checking `sσ ≻ uσ`
TEST_SIMPLIFICATION(demod_basic_06,
    ALASCA_Demod_TestCase<CoherenceDemodConf<RatTraits>>()
      .simplifyWith({    clause(   { isInt(f(x) + f(y))  }   ) })
      .toSimplify  ({    clause(   { p(floor(f(a) + f(b))) }   ) })
      .expectNotApplicable()
    )



// // checking `sσ ≻ uσ`
// TEST_SIMPLIFICATION(demod_ir_basic_01,
//     ALASCA_Demod_TestCase<IndequalityDemodulation<RatTraits>>()
//       .simplifyWith({    clause(   { isInt(f(x) + f(y))  }   ) })
//       .toSimplify  ({    clause(   { p(floor(f(a) + f(b))) }   ) })
//       .expectNotApplicable()
//     )

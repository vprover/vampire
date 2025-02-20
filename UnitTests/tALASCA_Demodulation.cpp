/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Test/SyntaxSugar.hpp"
#include "Inferences/ALASCA/FwdDemodulation.hpp"
#include "Inferences/ALASCA/BwdDemodulation.hpp"

#include "Test/SyntaxSugar.hpp"
#include "Test/FwdBwdSimplificationTester.hpp"
#include "Test/AlascaTestUtils.hpp"

using namespace std;
using namespace Kernel;
using namespace Inferences;
using namespace Test;
using namespace Indexing;
using namespace Inferences::ALASCA;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// TEST CASES 
/////////////////////////////////////

#define SUGAR(Num)                                                                                  \
  NUMBER_SUGAR(Num)                                                                                 \
  DECL_DEFAULT_VARS                                                                                 \
  DECL_CONST(a, Num)                                                                                \
  DECL_CONST(b, Num)                                                                                \
  DECL_CONST(c, Num)                                                                                \
  DECL_FUNC(f, {Num}, Num)                                                                          \
  DECL_FUNC(g, {Num, Num}, Num)                                                                     \
  DECL_PRED(p, {Num})                                                                               \
  DECL_PRED(p0, {})                                                                                 \
  DECL_PRED(r, {Num,Num})                                                                           \

#define MY_SYNTAX_SUGAR SUGAR(Rat) mkAlascaSyntaxSugar(Rat ## Traits{});

#define UWA_MODE Options::UnificationWithAbstraction::ALASCA_MAIN

inline auto ALASCA_Demod_TestCase()  {
  return FwdBwdSimplification:: TestCase()
    .fwd(new FwdDemodulation(testAlascaState(UWA_MODE)))
    .bwd(new BwdDemodulation(testAlascaState(UWA_MODE)))
    .fwdIdx({ new AlascaIndex<Demodulation::Lhs>() })
    .bwdIdx({ new AlascaIndex<Demodulation::Rhs>() });
}

// ±ks + t ≈ 0          C[sσ]
// ============================
//         C[sσ -> (∓ (1/k) t)σ]
// where
// • sσ is strictly max. in terms(s + t)σ 
// • C[sσ] ≻ (±ks + t ≈ 0)σ

/////////////////////////////////////////////////////////
// Basic tests
//////////////////////////////////////

TEST_SIMPLIFICATION(basic01,
    ALASCA_Demod_TestCase()
      .simplifyWith({    clause(   { 0 == f(a) - a  }   ) })
      .toSimplify  ({    clause(   { p(f(a))        }   ) })
      .expected(    {    clause(   { p(  a )        }   ) })
    )

TEST_SIMPLIFICATION(basic01b,
    ALASCA_Demod_TestCase()
      .simplifyWith({    clause(   { 0 == -f(a) + a  }   ) })
      .toSimplify  ({    clause(   { p(f(a))         }   ) })
      .expected(    {    clause(   { p(  a )         }   ) })
    )


TEST_SIMPLIFICATION(basic02,
    ALASCA_Demod_TestCase()
      .simplifyWith({    clause(   { 0 == f(a) - a   }   )
                    ,    clause(   { 0 == g(b,a) - b }   ) })
      .toSimplify  ({    clause(   { r(f(a), f(b))   }   ) })
      .expected(    {    clause(   { r(  a , f(b))   }   ) })
      .justifications({  clause(   {  0 == f(a) - a  }   ) })
    )

TEST_SIMPLIFICATION(basic03,
    ALASCA_Demod_TestCase()
      .simplifyWith({    clause(   { 0 == f(x) - x      }   ) })
      .toSimplify  ({    clause(   { r(f(a), f(b))      }   ) })
      .expected(    {    clause(   { r(f(a),   b )      }   ) })
    )

TEST_SIMPLIFICATION(basic04,
    ALASCA_Demod_TestCase()
      .simplifyWith({    clause(   { 0 == f(x) - x }   ) })
      .toSimplify  ({    clause(   { p(f(a))       }   ) , clause(   { p(f(b)) }   ) })
      .expected(    {    clause(   { p(  a )       }   ) , clause(   { p(  b ) }   ) })
    )

TEST_SIMPLIFICATION(basic05,
    ALASCA_Demod_TestCase()
      .simplifyWith({    clause(   { 0 == f(a) - a }   ), clause(   { 0 == f(b) - b }   ) })
      .toSimplify  ({    clause(   { p(f(a)) }         ), clause(   { p(f(b)) }         ) })
      .expected(    {    clause(   { p(  a ) }         ), clause(   { p(  b ) }         ) })
    )

TEST_SIMPLIFICATION(basic06,
    ALASCA_Demod_TestCase()
      .simplifyWith({    clause(   { 0 == f(a) - a }   ), clause(   { 0 == f(b) - b }   ) })
      .toSimplify  ({    clause(   { p(f(a)) }         ), clause(   { p(f(f(a))) }         ) })
      .expected(    {    clause(   { p(  a ) }         ), clause(   { p(  f(a) ) }         ) })
      .justifications({  clause(   {  0 == f(a) - a  }   ) })
    )

TEST_SIMPLIFICATION(basic07,
    ALASCA_Demod_TestCase()
      .simplifyWith({    clause(   { 0 == g(a, x) - x      }   ) })
      .toSimplify  ({    clause(   { p(g(a,b))             }   ) })
      .expected(    {    clause(   { p(    b )             }   ) })
    )

TEST_SIMPLIFICATION(basic08,
    ALASCA_Demod_TestCase()
      .simplifyWith({    clause(   { 0 == g(a, x) - x      }   ) })
      .toSimplify  ({    clause(   { p(g(y,b))             }   ) })
      .expected(      { /* nothing */ })
      .justifications({ /* nothing */ }) 
    )

TEST_SIMPLIFICATION(basic09,
    ALASCA_Demod_TestCase()
      .simplifyWith({    clause(   { 0 == frac(1,3) * f(g(a,a)) - a  }   ) })
      .toSimplify  ({    clause(   { p( f(g(a,a)))                   }   ) })
      .expected(    {    clause(   { p(3 * a)                        }   ) })
    )

// checking `C[sσ] ≻ (±ks + t ≈ 0)σ`
TEST_SIMPLIFICATION(ordering01,
    ALASCA_Demod_TestCase()
      .simplifyWith({    clause(   { 0 == f(x) + g(x,x) }   ) })
      .toSimplify  ({    clause(   { 0 == g(a,a)    }   ) })
      .expected(    {                /* nothing */        })
      .justifications({              /* nothing */        }) 
    )

// checking `sσ ≻ terms(t)σ`
TEST_SIMPLIFICATION(ordering02,
    ALASCA_Demod_TestCase()
      .simplifyWith({    clause(   { 0 == f(x) + g(y,y) }       ) })
      .toSimplify  ({    clause(   { 0 == g(a,a) + f(x) + a }   ) })
      .expected(    {                /* nothing */        })
      .justifications({              /* nothing */        }) 
    )

// checking `sσ ≻ terms(t)σ`
TEST_SIMPLIFICATION(sum01,
    ALASCA_Demod_TestCase()
      .simplifyWith({    clause(   { 0 == x + g(x,x) + a }       ) })
      .toSimplify  ({    clause(   { p(g(f(f(a)),f(f(a))))  }   ) })
      .expected(    {    clause(   { p(    - a - f(f(a)) )  }   ) })
    )

TEST_SIMPLIFICATION(sum02,
    ALASCA_Demod_TestCase()
      .simplifyWith({    clause(   { 0 == x + g(x,x) }       ) })
      .toSimplify  ({    clause(   { p(g(f(f(a)),f(f(a))))  }   ) })
      .expected(    {    clause(   { p(    - f(f(a))     )  }   ) })
    )

TEST_SIMPLIFICATION(sum03,
    ALASCA_Demod_TestCase()
      .simplifyWith({    clause(   { 0 == a + g(x,x) }       ) })
      .toSimplify  ({    clause(   { p(g(f(f(a)),f(f(a))))  }   ) })
      .expected(    {    clause(   { p(    - a           )  }   ) })
    )


TEST_SIMPLIFICATION(bug01,
    ALASCA_Demod_TestCase()
      .simplifyWith({    clause(   { 0 == g(x, y) - y  }   ) })
      .toSimplify  ({    clause(   { p(g(z,a))         }   ) })
      .expected(    {    clause(   { p(    a )         }   ) })
    )


TEST_SIMPLIFICATION(misc01,
    ALASCA_Demod_TestCase()
      .simplifyWith({    clause(   { 0 == a  }   ) })
      .toSimplify  ({    clause(   { ~p0(), a == b }   ) })
      .expected(    {    clause(   { ~p0(), b == 0 }   ) })
    )


TEST_SIMPLIFICATION(misc02,
    ALASCA_Demod_TestCase()
      .simplifyWith({    clause(   { 0 == b  }   ) })
      .toSimplify  ({    clause(   { ~p0(), a == b }   ) })
      .expected(    {    clause(   { ~p0(), a == 0 }   ) })
    )


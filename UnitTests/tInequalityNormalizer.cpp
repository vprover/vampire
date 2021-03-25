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
#include "Indexing/TermSharing.hpp"
#include "Inferences/InequalityResolution.hpp"
#include "Inferences/InterpretedEvaluation.hpp"
#include "Kernel/Ordering.hpp"
#include "Inferences/PolynomialEvaluation.hpp"
#include "Inferences/Cancellation.hpp"

#include "Kernel/LaKbo.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Test/TestUtils.hpp"
#include "Lib/Coproduct.hpp"
#include "Test/SimplificationTester.hpp"
#include "Test/GenerationTester.hpp"
#include "Kernel/KBO.hpp"
#include "Indexing/TermSubstitutionTree.hpp"
#include "Inferences/PolynomialEvaluation.hpp"

using namespace std;
using namespace Kernel;
using namespace Inferences;
using namespace Test;
using namespace Indexing;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// TEST CASES 
/////////////////////////////////////

#define SUGAR(Num)                                                                                            \
  __ALLOW_UNUSED(                                                                                             \
    NUMBER_SUGAR(Num)                                                                                         \
    DECL_DEFAULT_VARS                                                                                         \
    DECL_FUNC(f, {Num}, Num)                                                                                  \
    DECL_FUNC(g, {Num, Num}, Num)                                                                             \
    DECL_CONST(a, Num)                                                                                        \
    DECL_CONST(b, Num)                                                                                        \
    DECL_CONST(c, Num)                                                                                        \
    DECL_PRED(r, {Num,Num})                                                                                   \
  )                                                                                                           \



/////////////////////////////////////////////////////////
// Basic tests
//////////////////////////////////////

struct TestCase 
{
  Literal* in;
  Literal* out;

  template<class NumTraits>
  void run() {
    auto ord = LaKbo(KBO::testKBO());
    auto norm = InequalityNormalizer(PolynomialEvaluation(ord));
    auto result_ = norm.normalize<NumTraits>(in).unwrap();
    auto result = result_.value.denormalize();
    if (!TestUtils::eqModAC(out, result)) {
      std::cout << "\r" << endl;
      std::cout << "\r[   input  ]" << pretty(in) << endl;
      std::cout << "\r[ expected ]" << pretty(out) << endl;
      std::cout << "\r[  result  ]" << pretty(result) << endl;
      exit(-1);
    }
  }
};

#define TEST_CASE(Num, name, ...)                                                                             \
  TEST_FUN(name ## _ ## Num) {                                                                                \
    SUGAR(Num)                                                                                                \
    __VA_ARGS__.run<Num ## Traits>();                                                                         \
  }                                                                                                           \

#define TEST_FRAC(...)                                                                                        \
    TEST_CASE(Rat , __VA_ARGS__)                                                                              \
    TEST_CASE(Real, __VA_ARGS__)                                                                              \

#define TEST_INT(...)                                                                                         \
    TEST_CASE(Int, __VA_ARGS__)                                                                               \

#define TEST_ALL(...)                                                                                         \
    TEST_CASE(Int , __VA_ARGS__)                                                                              \
    TEST_CASE(Rat , __VA_ARGS__)                                                                              \
    TEST_CASE(Real, __VA_ARGS__)                                                                              \


TEST_ALL(strict_01, 
    TestCase {
      .in  =  f(a) < 0,
      .out = -f(a) > 0,
    })

TEST_ALL(strict_02, 
    TestCase {
      .in  =  0 > x,
      .out = -x > 0,
    })

TEST_ALL(strict_03, 
    TestCase {
      .in  = a > b,
      .out = a + -b > 0,
    })

TEST_ALL(strict_04, 
    TestCase {
      .in  = a + b > 0,
      .out = a + b > 0,
    })

///////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////

TEST_INT(lax_01, 
    TestCase {
      .in  = f(a) <= 0,
      .out = 1 + -f(a) > 0,
    })

TEST_INT(lax_02, 
    TestCase {
      .in  =  0 >= x,
      .out = -x + 1 > 0,
    })

TEST_INT(lax_03, 
    TestCase {
      .in  = a >= b,
      .out = a - b + 1 > 0,
    })

TEST_INT(lax_04, 
    TestCase {
      .in  = a + b >= 0,
      .out = a + b + 1 > 0,
    })


///////////////////////////////////////////////////////////////////////////////////////////////////////

TEST_FRAC(lax_01, 
    TestCase {
      .in  =  f(a) <= 0,
      .out = -f(a) >= 0,
    })

TEST_FRAC(lax_02, 
    TestCase {
      .in  =  0 >= x,
      .out = -x >= 0,
    })

TEST_FRAC(lax_03, 
    TestCase {
      .in  = a >= b,
      .out = a - b >= 0,
    })

TEST_FRAC(lax_04, 
    TestCase {
      .in  = a + b >= 0,
      .out = a + b >= 0,
    })

///////////////////////////////////////////////////////////////////////////////////////////////////////

TEST_ALL(bug_01, 
    TestCase {
      .in  = 0 * num(-1) + 2 * a * 1073741824 > 0,
      .out =               2 * a * 1073741824 > 0,
    })

TEST_INT(bug_02, 
    TestCase {
      .in  = ~(x <  0),
      //      (x >= 0),
      .out = x + 1 > 0,
    })

TEST_ALL(bug_03, 
    TestCase {
      .in  = g(a, x) + -2 * b * y > 0,
      .out = g(a, x) + -2 * b * y > 0,
   })
 
TEST_FRAC(bug_04, 
    TestCase {
      .in  = a + b + c >= 0,
      .out = a + b + c >= 0,
    })

TEST_FRAC(bug_05, 
    TestCase {
      .in  = a * b * c >= 0,
      .out = a * b * c >= 0,
    })


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
#include "Test/SimplificationTester.hpp"

#include "Inferences/PushUnaryMinus.hpp"

using namespace std;
using namespace Kernel;
using namespace Inferences;
using namespace Test;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// TEST UNIT INITIALIZATION
/////////////////////////////////////

#define MY_SIMPL_RULE   PushUnaryMinus
#define MY_SIMPL_TESTER Test::Simplification::SimplificationTester
#define MY_SYNTAX_SUGAR                                                                                       \
  NUMBER_SUGAR(Real)                                                                                          \
  DECL_DEFAULT_VARS                                                                                           \
  DECL_CONST(a, Real)                                                                                         \
  DECL_CONST(b, Real)                                                                                         \
  DECL_FUNC(f, {Real}, Real)                                                                                  \
  DECL_PRED(p, {Real})                                                                                        \
  DECL_PRED(q, {Real})                                                                                        \

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// TEST CASES
/////////////////////////////////////

TEST_SIMPLIFY(test_1,
    Simplification::Success()
      .input(    clause({  p(-(a + b))  }))
      .expected( clause({  p(-a + -b)  }))
    )

TEST_SIMPLIFY(test_2,
    Simplification::NotApplicable()
      .input( clause({ p(-a + -b) }))
    )

TEST_SIMPLIFY(test_3,
    Simplification::NotApplicable()
      .input( clause({ p(a) }))
    )

TEST_SIMPLIFY(test_4,
    Simplification::Success()
      .input(    clause({  p(-(a + b)), p(a)  }))
      .expected( clause({  p(-a + -b), p(a)  }))
    )

TEST_SIMPLIFY(test_5,
    Simplification::Success()
      .input(    clause({  p(a), p(-(a + b))  }))
      .expected( clause({  p(a), p(-a + -b)  }))
    )

// TEST_SIMPLIFY(test_3,
//     Simplification::Success()
//       .input(    clause({  3 * x != 6, x < x  }))
//       .expected( clause({  /* 2 < 2 */  }))
//     )
//
//   // 2x + y = x + y ==> 0 = 2x + y - x - y ==> 0 = x
// TEST_SIMPLIFY(test_4,
//     Simplification::Success()
//       .input(    clause({  2 * x + y != x + y, p(x) }))
//       .expected( clause({  p(0)  }))
//     )
//
// TEST_SIMPLIFY(test_uninterpreted,
//     Simplification::Success()
//       .input(    clause({  3 * f(x) != y, x < y  }))
//       .expected( clause({  x < 3 * f(x)  }))
//     )
//
//   // x!=4 \/ x+y != 5 \/ C[x]
//   //         4+y != 5 \/ C[4]
//   //                     C[4]
// TEST_SIMPLIFY(test_multiplesteps_1,
//     Simplification::Success()
//       .input(    clause({  x != 4, x + y != 5, x < f(x)  }))
//       .expected( clause({  4 < f(4)  }))
//     )
//
//   // x!=4 \/ x+y != 5 \/ C[x,y]
//   //         4+y != 5 \/ C[4,y]
//   //                     C[4,1]
// TEST_SIMPLIFY(test_multiplesteps_2,
//     Simplification::Success()
//       .input(    clause({  x != 4, x + y !=  5, x < f(y)  }))
//       .expected( clause({  4 < f(1)  }))
//     )
//
// TEST_SIMPLIFY(test_div,
//     Simplification::Success()
//       .input(    clause({  x / 3 != 4, p(x)  }))
//       .expected( clause({  p(12)  }))
//     )

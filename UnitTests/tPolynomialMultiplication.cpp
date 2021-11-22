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
#include "Test/GenerationTester.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Inferences/PolynomialMultiplication.hpp"


using namespace std;
using namespace Kernel;
using namespace Inferences;
using namespace Test;

// ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// ////// TEST UNIT INITIALIZATION
// /////////////////////////////////////
//
// /** 
//  * NECESSARY: We need a subclass of SimplificationTester
//  */
// class GveSimplTester : public Test::Simplification::SimplificationTester
// {
// public:
//
//   /**
//    * NECESSARY: performs the simplification
//    */
//   virtual Kernel::Clause* simplify(Kernel::Clause* in) const override 
//   {
//     auto rule = PolynomialMultiplication();
//     rule.siplify
//   }
//
//   /** 
//    * OPTIONAL: override how equality between clauses is checked. 
//    * Defaults to TestUtils::eqModAC(Clause const*, Clause const*).
//    */
//   virtual bool eq(Kernel::Clause const* lhs, Kernel::Clause const* rhs) const override
//   {
//     return TestUtils::eqModAC(lhs, rhs);
//   }
// };
//
// /**
//  * NECESSARY: Register our simpl tester as the one to use
//  */
// REGISTER_SIMPL_TESTER(GveSimplTester)
//
// /**
//  * NECESSARY: We neet to tell the simplification tester which syntax sugar to import for creating terms & clauses. 
//  * See Test/SyntaxSugar.hpp for which kinds of syntax sugar are available
//  */
// #define MY_SYNTAX_SUGAR                                                                                       \
//   NUMBER_SUGAR(Real)                                                                                          \
//   DECL_DEFAULT_VARS                                                                                           \
//   DECL_FUNC(f, {Real}, Real)                                                                                  \
//   DECL_PRED(p, {Real})                                                                                        \
//   DECL_PRED(q, {Real})                                                                                        \
//
// ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// ////// TEST CASES
// /////////////////////////////////////
//
// TEST_SIMPLIFY(gve_test_1,
//     /** 
//      * Runs our registered SimplificationTester on .input,
//      * and checks if the output equals .expected.
//      */
//     Simplification::Success()
//       .input(    clause({  3 * x != 6, x < y  }))
//       .expected( clause({  2 < y  }))
//     )
//
// TEST_SIMPLIFY(gve_test_2,
//     /** 
//      * Runs our registered SimplificationTester on .input,
//      * and fails if any simplification is performed.
//      */
//     Simplification::NotApplicable()
//       .input( clause({ 3 * x == 6, x < y }))
//     )
//
// TEST_SIMPLIFY(gve_test_3,
//     Simplification::Success()
//       .input(    clause({  3 * x != 6, x < x  }))
//       .expected( clause({  /* 2 < 2 */  }))
//     )
//
//   // 2x + y = x + y ==> 0 = 2x + y - x - y ==> 0 = x
// TEST_SIMPLIFY(gve_test_4,
//     Simplification::Success()
//       .input(    clause({  2 * x + y != x + y, p(x) }))
//       .expected( clause({  p(0)  }))
//     )
//
// TEST_SIMPLIFY(gve_test_uninterpreted,
//     Simplification::Success()
//       .input(    clause({  3 * f(x) != y, x < y  }))
//       .expected( clause({  x < 3 * f(x)  }))
//     )
//
//   // x!=4 \/ x+y != 5 \/ C[x]
//   //         4+y != 5 \/ C[4]
//   //                     C[4]
// TEST_SIMPLIFY(gve_test_multiplesteps_1,
//     Simplification::Success()
//       .input(    clause({  x != 4, x + y != 5, x < f(x)  }))
//       .expected( clause({  4 < f(4)  }))
//     )
//
//   // x!=4 \/ x+y != 5 \/ C[x,y]
//   //         4+y != 5 \/ C[4,y]
//   //                     C[4,1]
// TEST_SIMPLIFY(gve_test_multiplesteps_2,
//     Simplification::Success()
//       .input(    clause({  x != 4, x + y !=  5, x < f(y)  }))
//       .expected( clause({  4 < f(1)  }))
//     )
//
// TEST_SIMPLIFY(gve_test_div,
//     Simplification::Success()
//       .input(    clause({  x / 3 != 4, p(x)  }))
//       .expected( clause({  p(12)  }))
//     )

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// TEST CASES for generating inferences
/////////////////////////////////////

#define MY_SYNTAX_SUGAR                                                                                       \
  NUMBER_SUGAR(Real)                                                                                          \
  DECL_DEFAULT_VARS                                                                                           \
  DECL_CONST(a, Real)                                                                                         \
  DECL_CONST(b, Real)                                                                                         \
  DECL_CONST(c, Real)                                                                                         \
  DECL_FUNC(f, {Real}, Real)                                                                                  \
  DECL_PRED(p, {Real})                                                                                        \
  DECL_PRED(q, {Real})                                                                                        \


REGISTER_GEN_TESTER(Test::Generation::GenerationTester<PolynomialMultiplication>)

TEST_GENERATION(test_01,
    Generation::AsymmetricCase()
      .input(            clause({  p(  (y + x) * (a + x)  )  })   )
      .expected(exactly( clause({  p(x*x + x*a + x*y + a*y)  })  ))
      .premiseRedundant(false)
    )

// TODO write more tests

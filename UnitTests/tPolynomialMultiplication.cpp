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

TEST_GENERATION(single_var,
    Generation::TestCase()
      .input(           clause({ p(x) }) )
      .expected(exactly(  clause({ p(x) })))
      .premiseRedundant(false)
    )

TEST_GENERATION(single_func,
    Generation::TestCase()
      .input(           clause({ p(f(x)) }) )
      .expected(exactly(  clause({ p(f(x)) })))
      .premiseRedundant(false)
    )

TEST_GENERATION(single_const,
    Generation::TestCase()
      .input(           clause({ p(1) }) )
      .expected(exactly(  clause({ p(1) })))
      .premiseRedundant(false)
    )

TEST_GENERATION(already_norm,
     Generation::TestCase()
       .input(clause({            p((x*y) + x + (a*x*y)) }))
       .expected(exactly(clause({ p((x*y) + x + (a*x*y)) })))
       .premiseRedundant(false)
     )

TEST_GENERATION(monom_multiply,
     Generation::TestCase()
        .input(clause({             p(x*(a+x))}))
        .expected(exactly(clause({ p((a*x) + (x*x)) })))
        .premiseRedundant(false)
     )

TEST_GENERATION(poly_multiply,
     Generation::TestCase()
         .input(clause({            p((y+x+a) * (b+c)) }))
         .expected(exactly(clause( {p((y*b) + (x*b) + (a*b) + (y*c) + (x*c) + (a*c))} )))
         .premiseRedundant(false)
     )

TEST_GENERATION(resolve_func_term,
      Generation::TestCase()
         .input(clause({            p((a+x) * f((a+x)*(b+x))) }))
         .expected(exactly(clause({ p((a*f((a*b) + (a*x) + (b*x) + (x*x))) + (x*f((a*b) + (a*x) + (b*x) + (x*x))) ) })))
      )

TEST_GENERATION(two_in_a_row,
    Generation::TestCase()
      .input(            clause({  p(  (y + x) * (a + x)  )  })   )
      .expected(exactly( clause({  p(x*x + x*a + x*y + a*y)  })  ))
      .premiseRedundant(false)
    )

TEST_GENERATION(three_in_a_row,
    Generation::TestCase()
      .input(            clause({  p((y + x) * (a + x) * (a+f(b)))  })   )
      .expected(exactly( clause({  p((y * a * a) + (y * x * a) + (x * a * a) + (x * x * a) + (y * a * f(b)) + (y * x * f(b)) + (x * a * f(b)) + (x * x * f(b)))  })  ))
      .premiseRedundant(false)
    )

TEST_GENERATION(nested_poly,
    Generation::TestCase()
      .input(            clause({  p((x * (y * (z + a))))  })   )
      .expected(exactly( clause({  p((x * y * z) + (x * y * a))  })  ))
      .premiseRedundant(false)
    )

TEST_GENERATION(constant_summand,
    Generation::TestCase()
      .input(            clause({  p(a * (y + 2))  })   )
      .expected(exactly( clause({  p((a * y) + (2*a))  })  ))
      .premiseRedundant(false)
    )
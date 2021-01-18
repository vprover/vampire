
  /*
   * File tGaussianElimination.cpp.
   *
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
#include "Inferences/GaussianVariableElimination.hpp"
#include "Inferences/InterpretedEvaluation.hpp"
#include "Kernel/Ordering.hpp"
#include "Inferences/PolynomialEvaluation.hpp"
#include "Inferences/Cancellation.hpp"

#include "Test/SyntaxSugar.hpp"
#include "Test/TestUtils.hpp"
#include "Lib/Coproduct.hpp"
#include "Test/SimplificationTester.hpp"
#include "Test/GenerationTester.hpp"
#include "Kernel/KBO.hpp"

using namespace std;
using namespace Kernel;
using namespace Inferences;
using namespace Test;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// TEST UNIT INITIALIZATION
/////////////////////////////////////

/** 
 * NECESSARY: We need a subclass of SimplificationTester
 */
class GveSimplTester : public Test::Simplification::SimplificationTester
{
public:

  /**
   * NECESSARY: performs the simplification
   */
  virtual Kernel::Clause* simplify(Kernel::Clause* in) const override 
  {
    KBO ord = KBO::testKBO();
    auto simpl = [](Clause* cl)  -> Clause*
    {
      static PolynomialEvaluation eval(*Ordering::tryGetGlobalOrdering());
      static Cancellation cancel(*Ordering::tryGetGlobalOrdering());
      return cancel.asISE().simplify(eval.asISE().simplify(cl));
    };
    static GaussianVariableElimination gve = GaussianVariableElimination(/* generateGuards */ false);

    /* applies gve and evaluation until they're not applicable anymore */
    Kernel::Clause* last = simpl(in);
    Kernel::Clause* latest = simpl(in);
    do {
      last = latest;
      latest = simpl(gve.asISE().simplify(last));
    } while (latest != last);
    return latest;
  }

  /** 
   * OPTIONAL: override how equality between clauses is checked. 
   * Defaults to TestUtils::eqModAC(Clause const*, Clause const*).
   */
  virtual bool eq(Kernel::Clause const* lhs, Kernel::Clause const* rhs) const override
  {
    return TestUtils::eqModAC(lhs, rhs);
  }
};

/**
 * NECESSARY: Register our simpl tester as the one to use
 */
REGISTER_SIMPL_TESTER(GveSimplTester)

/**
 * NECESSARY: We neet to tell the simplification tester which syntax sugar to import for creating terms & clauses. 
 * See Test/SyntaxSugar.hpp for which kinds of syntax sugar are available
 */
#define MY_SYNTAX_SUGAR                                                                                       \
  NUMBER_SUGAR(Real)                                                                                          \
  DECL_DEFAULT_VARS                                                                                           \
  DECL_FUNC(f, {Real}, Real)                                                                                  \
  DECL_PRED(p, {Real})                                                                                        \
  DECL_CONST(c, Real)                                                                                        \
  DECL_PRED(q, {Real})                                                                                        \

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// TEST CASES
/////////////////////////////////////

TEST_SIMPLIFY(gve_test_1,
    /** 
     * Runs our registered SimplificationTester on .input,
     * and checks if the output equals .expected.
     */
    Simplification::Success()
      .input(    clause({  3 * x != 6, x < y  }))
      .expected( clause({  2 < y  }))
    )

TEST_SIMPLIFY(gve_test_2,
    /** 
     * Runs our registered SimplificationTester on .input,
     * and fails if any simplification is performed.
     */
    Simplification::NotApplicable()
      .input( clause({ 3 * x == 6, x < y }))
    )

TEST_SIMPLIFY(gve_test_3,
    Simplification::Success()
      .input(    clause({  3 * x != 6, x < x  }))
      .expected( clause({  /* 2 < 2 */  }))
    )

  // 2x + y = x + y ==> 0 = 2x + y - x - y ==> 0 = x
TEST_SIMPLIFY(gve_test_4,
    Simplification::Success()
      .input(    clause({  2 * x + y != x + y, p(x) }))
      .expected( clause({  p(0)  }))
    )

TEST_SIMPLIFY(gve_test_uninterpreted,
    Simplification::Success()
      .input(    clause({  3 * f(x) != y, x < y  }))
      .expected( clause({  x < 3 * f(x)  }))
    )

  // x!=4 \/ x+y != 5 \/ C[x]
  //         4+y != 5 \/ C[4]
  //                     C[4]
TEST_SIMPLIFY(gve_test_multiplesteps_1,
    Simplification::Success()
      .input(    clause({  x != 4, x + y != 5, x < f(x)  }))
      .expected( clause({  4 < f(4)  }))
    )

  // x!=4 \/ x+y != 5 \/ C[x,y]
  //         4+y != 5 \/ C[4,y]
  //                     C[4,1]
TEST_SIMPLIFY(gve_test_multiplesteps_2,
    Simplification::Success()
      .input(    clause({  x != 4, x + y !=  5, x < f(y)  }))
      .expected( clause({  4 < f(1)  }))
    )

TEST_SIMPLIFY(gve_test_div,
    Simplification::Success()
      .input(    clause({  x / 3 != 4, p(x)  }))
      .expected( clause({  p(12)  }))
    )

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// TEST CASES for generating inferences
/////////////////////////////////////

static GaussianVariableElimination gve  = GaussianVariableElimination(true);
struct MyGenerationTester : public Test::Generation::GenerationTester<LfpRule<GaussianVariableElimination>> {
  MyGenerationTester() : Test::Generation::GenerationTester<LfpRule<GaussianVariableElimination>>(/* generateGuards */ true) {}
};
REGISTER_GEN_TESTER(MyGenerationTester) 

TEST_GENERATION(test_redundancy_01,
    Generation::TestCase()
      .input(    clause({  x != 4, p(x)  }))
      .expected(exactly(
            clause({  p(4)  })
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION(test_redundancy_02,
    Generation::TestCase()
      .input(     clause({  x != 4, p(y)  }))
      .expected( exactly(
            clause({  p(y)  })
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(test_redundancy_03,
    Generation::TestCase()
      .input(     clause({   x != 4, p(y), q(x)  }))
      .expected( exactly(
            clause({  p(y), q(4)  })
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION(test_redundancy_04,
    Generation::TestCase()
      .input(     clause({   x != 4, p(x), q(x)  }))
      .expected( exactly(
            clause({  p(4), q(4)  })
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION(test_redundancy_05,
    Generation::TestCase()
      .input(     clause({   x != 4, p(y), q(y)  }))
      .expected( exactly(
            clause({  p(y), q(y)  })
      ))
      .premiseRedundant(true)
    )


TEST_GENERATION(test_redundancy_06,
    Generation::TestCase()
      .input(     clause({  y != 5, x != 4, p(x), q(y)  }))
      .expected( exactly(
            clause({  p(4), q(5)  })
      ))
      .premiseRedundant(false)
    )

// I found potential issue with adding guards in gve:
//
// As we discussed before there may be multiple options of how to perform the rewriting of the equality. 
//
// Consider this clause: 
// ```
// (y * f(c)) + (x * 4) != 0 4 \/ p(x, y)
// ```
//
// Option 1)
// ```
//  (y * f(c)) + (x * 4) !=  0 \/ p(x, y)
// ======================================= rewriting to y != (x * -4) / f(c)
//    p(x,  (x * -4) / f(c)) \/ f(c) = 0
// ```
//
// Option 2)
// ```
//  (y * f(c)) + (x * 4) !=  0 \/ p(x, y)
// ======================================= rewriting to x != (-y * f(c))/4
//    p((-y * f(c))/4, y)
// ```
//
// Right now we just choose the first possible rebalancing (depth first; left to right), hence we'd choose Option 1). 
// But what I'd intuitively want is Option 2), because we don't need the guard there, hence it feels more general. 
// 
// So my question is the following: do you think Option 2 is better than Option 1? And if so, why how would you argue for that (in a paper)?
// If we'd prefer cases without guards over the ones with guards, I'd suggest we'd first try to apply the original gve, and if it fails we try to apply it with guards.
//
// What do you think?



TEST_GENERATION(test_redundancy_07,
    Generation::TestCase()
      .input(     clause({ c != f(c) * x, p(x)  }))
      .expected( exactly(
            clause({  p(c / f(c)), f(c) == 0 })
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION(test_redundancy_08,
    Generation::TestCase()
      .input(     clause({ c !=  x / f(c), p(x)  }))
      .expected( exactly(
            clause({  p(c * f(c)), f(c) == 0 })
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION(test_redundancy_09,
    Generation::TestCase()
      .input(     clause({ c != f(c) / x, p(x)  }))
      //                 { c * x != f(c) , p(x), x == 0  }
      //                 { x != f(c) / c , p(x), x == 0, c == 0  }
      .expected( exactly(
            clause({ p(f(c) / c), x == 0, c == 0 })
      ))
      .premiseRedundant(false)
    )

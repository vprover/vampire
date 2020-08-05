
#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Indexing/TermSharing.hpp"
#include "Inferences/GaussianVariableElimination.hpp"
#include "Inferences/InterpretedEvaluation.hpp"
#include "Kernel/Ordering.hpp"
#include "Inferences/PolynomialNormalization.hpp"

#include "Test/SyntaxSugar.hpp"
#include "Test/TestUtils.hpp"
#include "Lib/Coproduct.hpp"
#include "Test/SimplificationTester.hpp"

using namespace std;
using namespace Kernel;
using namespace Inferences;
using namespace Test;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// TEST UNIT INITIALIZATION
/////////////////////////////////////

/** 
 * NECESSARY: as for every test unit we need to specify a name, and initialize the unit 
 */
#define UNIT_ID GaussianVariableElimination
UT_CREATE;

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
    struct FakeOrdering : Kernel::Ordering {
      virtual Result compare(Literal* l, Literal* r) const override { 
        if (l == r) {
          return Kernel::Ordering::EQUAL; 
        } else {
          return Kernel::Ordering::LESS; 
        }
      }
      virtual Result compare(TermList, TermList) const override {ASSERTION_VIOLATION}
      virtual Comparison compareFunctors(unsigned, unsigned) const override {ASSERTION_VIOLATION}
    };
    static FakeOrdering ord;
    static GaussianVariableElimination gve = GaussianVariableElimination();
    static PolynomialNormalization eval(ord);

    /* applies gve and evaluation until they're not applicable anymore */
    Kernel::Clause* last = eval.simplify(in);
    Kernel::Clause* latest = eval.simplify(in);
    do {
      last = latest;
      latest = eval.simplify(gve.simplify(last));
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
#define SIMPL_SUGAR                                                                                                     \
  THEORY_SYNTAX_SUGAR(REAL)                                                                                             \
  THEORY_SYNTAX_SUGAR_FUN(f, 1)                                                                                         \
  THEORY_SYNTAX_SUGAR_PRED(p, 1)                                                                                        \

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// TEST CASES
/////////////////////////////////////

TEST_SIMPLIFY(gve_test_1,
    /** 
     * Runs our registered SimplificationTester on .input,
     * and checks if the output equals .expected.
     */
    Simplification::Success {
      .input    = clause({  3 * x != 6, x < y  }),
      .expected = clause({  2 < y  }),
    })

TEST_SIMPLIFY(gve_test_2,
    /** 
     * Runs our registered SimplificationTester on .input,
     * and fails if any simplification is performed.
     */
    Simplification::NotApplicable {
      .input = clause({ 3 * x == 6, x < y }),
    })

TEST_SIMPLIFY(gve_test_3,
    Simplification::Success {
      .input    = clause({  3 * x != 6, x < x  }),
      .expected = clause({  /* 2 < 2 */  }),
    })

  // 2x + y = x + y ==> 0 = 2x + y - x - y ==> 0 = x
TEST_SIMPLIFY(gve_test_4,
    Simplification::Success {
      .input    = clause({  2 * x + y != x + y, p(x) }),
      .expected = clause({  p(0)  }),
    })

TEST_SIMPLIFY(gve_test_uninterpreted,
    Simplification::Success {
      .input    = clause({  3 * f(x) != y, x < y  }),
      .expected = clause({  x < 3 * f(x)  }),
    })

  // x!=4 \/ x+y != 5 \/ C[x]
  //         4+y != 5 \/ C[4]
  //                     C[4]
TEST_SIMPLIFY(gve_test_multiplesteps_1,
    Simplification::Success {
      .input    = clause({  x != 4, x + y != 5, x < f(x)  }),
      .expected = clause({  4 < f(4)  }),
    })

  // x!=4 \/ x+y != 5 \/ C[x,y]
  //         4+y != 5 \/ C[4,y]
  //                     C[4,1]
TEST_SIMPLIFY(gve_test_multiplesteps_2,
    Simplification::Success {
      .input    = clause({  x != 4, x + y !=  5, x < f(y)  }),
      .expected = clause({  4 < f(1)  }),
    })

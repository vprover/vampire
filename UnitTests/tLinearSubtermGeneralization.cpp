
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

#define UNIT_ID LinearSubtermGeneralization
UT_CREATE;

class SimplificationTester : public Test::Simplification::SimplificationTester
{
public:

  virtual Kernel::Clause* simplify(Kernel::Clause* in) const override 
  {
    ASSERTION_VIOLATION //TODO
  }
};

REGISTER_SIMPL_TESTER(SimplificationTester)

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

TEST_SIMPLIFY(test01,
    /** 
     * Runs our registered SimplificationTester on .input,
     * and checks if the output equals .expected.
     */
    Simplification::Success {
      .input    = clause({  }), // TODO this is a dummy test
      .expected = clause({  }),
    })

TEST_SIMPLIFY(test02,
    /** 
     * Runs our registered SimplificationTester on .input,
     * and fails if any simplification is performed.
     */
    Simplification::NotApplicable {
      .input = clause({ }),// TODO this is a dummy test
    })

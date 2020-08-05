
#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Indexing/TermSharing.hpp"
#include "Inferences/GaussianVariableElimination.hpp"
#include "Inferences/InterpretedEvaluation.hpp"
#include "Kernel/Ordering.hpp"
#include "Inferences/ArithmeticSubtermGeneralization.hpp"

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
    return ArithmeticSubtermGeneralization().simplify(in);
  }
};

REGISTER_SIMPL_TESTER(SimplificationTester)

#define SIMPL_SUGAR_(num)                                                                                               \
  THEORY_SYNTAX_SUGAR(num)                                                                                              \
  THEORY_SYNTAX_SUGAR_PRED(p, 1)                                                                                        \
  THEORY_SYNTAX_SUGAR_PRED(p1, 1)                                                                                       \
  THEORY_SYNTAX_SUGAR_PRED(p2, 1)                                                                                       \
  THEORY_SYNTAX_SUGAR_PRED(p3, 1)                                                                                       \
  THEORY_SYNTAX_SUGAR_PRED(r, 2)                                                                                        \

#define TEST_SIMPLIFY_FRACTIONAL(name, ...)                                                                             \
    TEST_SIMPLIFY_WITH_SUGAR(CAT(name, _REAL), SIMPL_SUGAR_(REAL), __VA_ARGS__)                                         \
    TEST_SIMPLIFY_WITH_SUGAR(CAT(name, _RAT ), SIMPL_SUGAR_(RAT ), __VA_ARGS__)                                         \

#define TEST_SIMPLIFY_INTEGER(name, ...)                                                                                \
    TEST_SIMPLIFY_WITH_SUGAR(CAT(name, _INT ), SIMPL_SUGAR_(INT ), __VA_ARGS__)                                         \

#define TEST_SIMPLIFY_NUMBER(name, ...)                                                                                 \
    TEST_SIMPLIFY_FRACTIONAL(name, __VA_ARGS__)                                                                         \
    TEST_SIMPLIFY_INTEGER(name, __VA_ARGS__)                                                                            \

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// TEST CASES
/////////////////////////////////////

TEST_SIMPLIFY_FRACTIONAL(single_var_01,
    Simplification::Success {
      .input    = clause({ p(3 * x) }),
      .expected = clause({ p(x) }),
    })

TEST_SIMPLIFY_INTEGER(single_var_01,
    Simplification::NotApplicable {
      .input    = clause({ p(3 * x) }),
    })

TEST_SIMPLIFY_NUMBER(single_var_02,
    Simplification::Success {
      .input    = clause({ p(x + 7) }),
      .expected = clause({ p(x) }),
    })

TEST_SIMPLIFY_FRACTIONAL(single_var_03,
    Simplification::Success {
      .input    = clause({ p(3 * x + 7) }), 
      .expected = clause({ p(x) }),
    })

TEST_SIMPLIFY_INTEGER(single_var_03,
    Simplification::NotApplicable {
      .input    = clause({ p(3 * x + 7) }), 
    })

TEST_SIMPLIFY_FRACTIONAL(single_var_04,
    Simplification::Success {
      .input    = clause({ p(3 * x + 6) }), 
      .expected = clause({ p(x)         }),
    })

TEST_SIMPLIFY_INTEGER(single_var_04,
    Simplification::Success {
      .input    = clause({ p(3 * x + 6) }), 
      .expected = clause({ p(3 * x)     }),
    })

TEST_SIMPLIFY_FRACTIONAL(single_var_05,
    Simplification::Success {
      .input    = clause({ r(3 * x + 7, 3 * x + 7) }), 
      .expected = clause({ r(x, x) }),
    })

TEST_SIMPLIFY_INTEGER(single_var_05,
    Simplification::Success {
      .input    = clause({ r(5 * x + 10, 5 * x + 10) }), 
      .expected = clause({ r(5 * x, 5 * x) }),
    })

TEST_SIMPLIFY_INTEGER(single_var_06,
    Simplification::Success {
      .input    = clause({ r(4 * x + 20, 2 * x + 20) }), 
      //                    x -> x - 5
      .expected = clause({ r(4 * x     , 2 * x + 10) }),
    })

TEST_SIMPLIFY_INTEGER(single_var_07,
    Simplification::Success {
      .input    = clause({ r(4 * x + 20, 2 * x + -20) }), 
      //                    x -> x - 5
      .expected = clause({ r(4 * x     , 2 * x + -30) }),
    })

TEST_SIMPLIFY_INTEGER(single_var_08,
    Simplification::NotApplicable {
      .input    = clause({ p1(4 * x + 20), p2(2 * x + -20) }), 
      //             not { p1(4 * x     ), p2(2 * x + -30) } since the second predicate becomes bigger
    })

TEST_SIMPLIFY_FRACTIONAL(single_var_08,
    Simplification::Success {
      .input    = clause({ p1(4 * x + 20), p2(2 * x + -20) }), 
      //           ===>  { p1(2 * x + 20), p2(    x + -20) }), 
      //           ===>  { p1(2 * x     ), p2(    x + -30) }),  x -> x - 10
      .expected = clause({ p1(2 * x     ), p2(    x + -30) }),  
    })

TEST_SIMPLIFY_INTEGER(single_var_09,
    Simplification::NotApplicable {
      .input    = clause({ r(4 * x + 20, 2 * x + -20) }), 
    })

TEST_SIMPLIFY_FRACTIONAL(single_var_10,
    Simplification::Success {
      .input    = clause({ r(3 * x + 7, 3 * x + 5) }), 
      //          ====>  { r(    x + 7,     x + 5) }   
      //          ====>  { r(    x + 2,     x    ) }   
      .expected = clause({ r(x + 2, x) }),
    })

TEST_SIMPLIFY_NUMBER(single_var_11,
    Simplification::Success {
      .input    = clause({ r(    x +  7,    x + (-5) ) }), 
      .expected = clause({ r(    x     ,    x + (-12)) }),
      //           not   { r(    x + 12,    x        ) }   since the former is smaller wrt KBO
    })


TEST_SIMPLIFY_NUMBER(single_var_12,
    Simplification::NotApplicable {
      .input    = clause({ p(0 * x) }), 
    })

TEST_SIMPLIFY_NUMBER(single_var_13,
    Simplification::Success {
      .input    = clause({ p1(x + 3), p2(x + 7) }), 
      .expected = clause({ p1(x),     p2(x + 4) }), 
    })

TEST_SIMPLIFY_NUMBER(single_var_14,
    Simplification::Success {
      .input    = clause({ p1(x + 3), p2(x + 7), p3(x + 80) }), 
      .expected = clause({ p1(x    ), p2(x + 4), p3(x + 77) }), 
    })

TEST_SIMPLIFY_NUMBER(single_var_15,
    Simplification::NotApplicable {
      .input    = clause({ p1(x +  3), p2(x + -7) }), 
    })

TEST_SIMPLIFY_NUMBER(single_var_16,
    Simplification::Success {
      .input    = clause({ r(x + 3, x +  -7) }), 
      .expected = clause({ r(x    , x + -10) }), 
    })

TEST_SIMPLIFY_NUMBER(single_var_17,
    Simplification::Success {
      .input    = clause({ p1(x + (-3)), p2(x + (-7)) }), 
      .expected = clause({ p1(x)       , p2(x + (-4)) }), 
    })

TEST_SIMPLIFY_FRACTIONAL(multi_var_01,
    Simplification::Success {
      .input    = clause({ p(3 * x + 4 * y + 7 * z + 4) }),
      .expected = clause({ p(x) }), 
    })

TEST_SIMPLIFY_INTEGER(multi_var_01,
    Simplification::NotApplicable {
      .input    = clause({ p(3 * x + 4 * y + 7 * z + 4) }),
    })

TEST_SIMPLIFY_NUMBER(multi_var_02,
    Simplification::Success {
      .input    = clause({ p(x + 4 * y + 7 * z + 4) }),
      .expected = clause({ p(x) }), 
    })

TEST_SIMPLIFY_FRACTIONAL(multi_var_03,
    Simplification::Success {
      .input    = clause({ p1(3 * x + 4 * y + 7 * z + 4), p2(x + 4) }),
      //          ==>    { p1(3 * x +     y + 7 * z + 4), p2(x + 4) }) by (y -> 1/4 y)
      //          ==>    { p1(            y + 7 * z + 4), p2(x + 4) }) by (y -> -3*x + y)
      //          ==>    { p1(            y + 7 * z + 4), p2(x + 4) }) by (y -> -7*z + y)
      //          ==>    { p1(            y            ), p2(x    ) }) by (x -> x - 4)
      .expected = clause({ p1(y),                         p2(x) }), 
    })

TEST_SIMPLIFY_INTEGER(multi_var_03,
    Simplification::NotApplicable {
      .input    = clause({ p1(3 * x + 4 * y + 7 * z + 4), p2(x + 4) }),
    })

TEST_SIMPLIFY_NUMBER(multi_var_04,
    Simplification::Success {
      .input    = clause({ p1(3 * x +     y + 7 * z + 4), p2(x + 4) }),
      //          ==>    { p1(            y + 7 * z + 4), p2(x + 4) }) by (y -> -3*x + y)
      //          ==>    { p1(            y + 7 * z + 4), p2(x + 4) }) by (y -> -7*z + y)
      //          ==>    { p1(            y            ), p2(x    ) }) by (x -> x - 4)
      .expected = clause({ p1(y),                         p2(x) }), 
    })

TEST_SIMPLIFY_FRACTIONAL(multi_var_05,
    Simplification::Success {
      .input    = clause({ p1(3 * x + 2 * y), p2(3 * x + 2 * y) }),
      .expected = clause({ p1(x), p2(x) }), 
    })

TEST_SIMPLIFY_INTEGER(multi_var_05,
    Simplification::NotApplicable {
      .input    = clause({ p1(3 * x + 2 * y), p2(3 * x + 2 * y) }),
    })

TEST_SIMPLIFY_FRACTIONAL(multi_var_06,
    Simplification::Success {
      .input    = clause({ p1(3 * x + 2 * y), p2(3 * x + 2 * y + 1) }),
      .expected = clause({ p1(x), p2(x + 1) }), 
    })

TEST_SIMPLIFY_INTEGER(multi_var_06,
    Simplification::NotApplicable {
      .input    = clause({ p1(3 * x + 2 * y), p2(3 * x + 2 * y + 1) }),
    })

TEST_SIMPLIFY_FRACTIONAL(multi_var_07,
    Simplification::Success {
      .input    = clause({ p1(3 * x), p2(3 * x + 2 * y + 1) }),
      .expected = clause({ p1(x)    , p2(y) }), 
    })

TEST_SIMPLIFY_INTEGER(multi_var_07,
    Simplification::NotApplicable {
      .input    = clause({ p1(3 * x), p2(3 * x + 2 * y + 1) }),
    })

TEST_SIMPLIFY_FRACTIONAL(multi_var_08,
    Simplification::Success {
      .input    = clause({ p1(6 * x), p2(6 * x + 2 * y + 2) }),
      //                 { p1(6 * x), p2(        2 * y    ) }  by  y -> -3x + y - 1
      .expected = clause({ p1(    x), p2(            y    ) }), 
    })

TEST_SIMPLIFY_INTEGER(multi_var_08,
    Simplification::Success {
      .input    = clause({ p1(6 * x), p2(6 * x + 2 * y + 2) }),
      //                 { p1(6 * x), p2(        2 * y    ) }  by  y -> -3x + y - 1
      .expected = clause({ p1(6 * x), p2(        2 * y    ) }), 
    })

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
#include "Inferences/GaussianVariableElimination.hpp"
#include "Inferences/InterpretedEvaluation.hpp"
#include "Kernel/Ordering.hpp"
#include "Inferences/ArithmeticSubtermGeneralization.hpp"
#include "Inferences/PolynomialEvaluation.hpp"

#include "Test/SyntaxSugar.hpp"
#include "Test/TestUtils.hpp"
#include "Lib/Coproduct.hpp"
#include "Test/SimplificationTester.hpp"
#include "Kernel/KBO.hpp"

using namespace std;
using namespace Kernel;
using namespace Inferences;
using namespace Test;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// TEST UNIT INITIALIZATION
/////////////////////////////////////

#define PHASE 1

class SimplificationTester : public Test::Simplification::SimplificationTester
{
public:

  // virtual bool eq(Kernel::Clause const* lhs, Kernel::Clause const* rhs) const override
  // { return TestUtils::eqModACVar(lhs, rhs); }

  virtual Kernel::Clause* simplify(Kernel::Clause* in) const override 
  {
    auto ord = KBO::testKBO();
    Ordering::trySetGlobalOrdering(SmartPtr<Ordering>(&ord, true));
    auto apply = [](SimplifyingGeneratingInference1& simpl, Kernel::Clause* in) {
     auto out = simpl.asISE().simplify(in);
     // DEBUG("result: ", pretty(out));
     return out;
    };
    auto mulNum = NumeralMultiplicationGeneralization();
    auto mulVar = VariableMultiplicationGeneralization();
    auto varPower = VariablePowerGeneralization();
    auto add = AdditionGeneralization();
    Clause* last = nullptr;
    auto cur = in;
    do {
      last = cur;
      cur = apply(varPower, apply(mulVar,apply(add, apply(mulNum, cur))));
    } while (last != cur);
    return cur;
  }
};

REGISTER_SIMPL_TESTER(SimplificationTester)

#define SIMPL_SUGAR_(num)                                                                                     \
  NUMBER_SUGAR(num)                                                                                           \
  DECL_DEFAULT_VARS                                                                                           \
  DECL_CONST(a, num)                                                                                          \
  DECL_PRED(p , {num})                                                                                        \
  DECL_PRED(p1, {num})                                                                                        \
  DECL_PRED(p2, {num})                                                                                        \
  DECL_PRED(p3, {num})                                                                                        \
  DECL_PRED(r , {num, num})                                                                                   \
  DECL_FUNC(f,  {num}, num)                                                                                   \

#define TEST_SIMPLIFY_FRACTIONAL(name, ...)                                                                   \
    TEST_SIMPLIFY_WITH_SUGAR(CAT(name, _Real), SIMPL_SUGAR_(Real), __VA_ARGS__)                               \
    TEST_SIMPLIFY_WITH_SUGAR(CAT(name, _Rat ), SIMPL_SUGAR_(Rat ), __VA_ARGS__)                               \

#define TEST_SIMPLIFY_RATIONAL(name, ...)                                                                     \
    TEST_SIMPLIFY_WITH_SUGAR(CAT(name, _Rat ), SIMPL_SUGAR_(Rat ), __VA_ARGS__)                               \

#define TEST_SIMPLIFY_INTEGER(name, ...)                                                                      \
    TEST_SIMPLIFY_WITH_SUGAR(CAT(name, _Int ), SIMPL_SUGAR_(Int ), __VA_ARGS__)                               \

#define TEST_SIMPLIFY_REAL(name, ...)                                                                         \
    TEST_SIMPLIFY_WITH_SUGAR(CAT(name, _Real), SIMPL_SUGAR_(Real), __VA_ARGS__)                               \

#define TEST_SIMPLIFY_NUMBER(name, ...)                                                                       \
    TEST_SIMPLIFY_FRACTIONAL(name, __VA_ARGS__)                                                               \
    TEST_SIMPLIFY_INTEGER(name, __VA_ARGS__)                                                                  \

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// TEST CASES
/////////////////////////////////////

#define PHASE 1

// Rule 1
TEST_SIMPLIFY_FRACTIONAL(single_var_01,
    Simplification::Success()
      .input(    clause({ p(3 * x) }))
      .expected( clause({ p(x) }))
    )

// Rule 1
TEST_SIMPLIFY_INTEGER(single_var_01,
    Simplification::NotApplicable()
      .input(    clause({ p(3 * x) }))
    )

// Rule 2
TEST_SIMPLIFY_NUMBER(single_var_02,
    Simplification::Success()
      .input(    clause({ p(x + 7) }))
      .expected( clause({ p(x) }))
    )

// Rule 1
// Rule 2
TEST_SIMPLIFY_FRACTIONAL(single_var_03,
    Simplification::Success()
      .input(    clause({ p(3 * x + 7) })) 
      .expected( clause({ p(x) }))
    )

// Rule 1
// Rule 2
TEST_SIMPLIFY_INTEGER(single_var_03,
    Simplification::NotApplicable()
      .input(    clause({ p(3 * x + 7) }))
    )

// Rule 1
// Rule 2
TEST_SIMPLIFY_FRACTIONAL(single_var_04,
    Simplification::Success()
      .input(    clause({ p(3 * x + 6) })) 
      .expected( clause({ p(x)         }))
    )

#if PHASE >= 2 
// Rule 1
// Rule 2

TEST_SIMPLIFY_INTEGER(single_var_04,
    Simplification::Success()
      .input(    clause({ p(3 * x + 6) })) 
      .expected( clause({ p(3 * x)     }))
    )

#endif // PHASE >= 2 

// Rule 1
// Rule 2
TEST_SIMPLIFY_FRACTIONAL(single_var_05,
    Simplification::Success()
      .input(    clause({ r(3 * x + 7, 3 * x + 7) })) 
      .expected( clause({ r(x, x) }))
    )

#if PHASE >= 3
TEST_SIMPLIFY_INTEGER(single_var_05,
    Simplification::Success()
      .input(    clause({ r(5 * x + 10, 5 * x + 10) })) 
      .expected( clause({ r(5 * x, 5 * x) }))
    )

TEST_SIMPLIFY_INTEGER(single_var_06,
    Simplification::Success()
      .input(    clause({ r(4 * x + 20, 2 * x + 20) })) 
      //(                    -) x - 5
      expected = clause({ r(4 * x     , 2 * x + 10) }),
    })

TEST_SIMPLIFY_INTEGER(single_var_07,
    Simplification::Success()
      .input(    clause({ r(4 * x + 20, 2 * x + -20) })) 
      //(                    -) x - 5
      expected = clause({ r(4 * x     , 2 * x + -30) }),
    })

TEST_SIMPLIFY_INTEGER(single_var_08,
    Simplification::NotApplicable()
      .input(    clause({ p1(4 * x + 20), p2(2 * x + -20) }))
      /             not { p1(4 * x     ), p2(2 * x + -30) } since the second predicate becomes bigger
    })

TEST_SIMPLIFY_FRACTIONAL(single_var_08,
    Simplification::Success()
      .input(    clause({ p1(4 * x + 20), p2(2 * x + -20) })) 
      //(           { p1(2 * x + 20), p2(    x + -20) }), 
      /           ===>  { p1(2 * x     ), p2(    x + -30) }),  x -> x - 10
      .expected = clause({ p1(2 * x     ), p2(    x + -30) }),  
    })

TEST_SIMPLIFY_INTEGER(single_var_09,
    Simplification::NotApplicable()
      .input(    clause({ r(4 * x + 20, 2 * x + -20) }))
    )

TEST_SIMPLIFY_FRACTIONAL(single_var_10,
    Simplification::Success()
      .input(    clause({ r(3 * x + 7, 3 * x + 5) })) 
      //(          { r(    x + 7,     x + 5) })  
      /          ====>  { r(    x + 2,     x    ) }   
      .expected = clause({ r(x + 2, x) }),
    })

TEST_SIMPLIFY_NUMBER(single_var_11,
    Simplification::Success()
      .input(    clause({ r(    x +  7,    x + (-5) ) })) 
      .expected( clause({ r(    x     ,    x + (-12)) }))
      /           not   { r(    x + 12,    x        ) }   since the former is smaller wrt KBO
    })
#endif // PHASE >= 3


TEST_SIMPLIFY_NUMBER(single_var_12,
    Simplification::NotApplicable()
      .input(    clause({ p(0 * x) }))
    )

#if PHASE >= 3 
TEST_SIMPLIFY_NUMBER(single_var_13,
    Simplification::Success()
      .input(    clause({ p1(x + 3), p2(x + 7) })) 
      .expected( clause({ p1(x),     p2(x + 4) })) 
    )

TEST_SIMPLIFY_NUMBER(single_var_14,
    Simplification::Success()
      .input(    clause({ p1(x + 3), p2(x + 7), p3(x + 80) })) 
      .expected( clause({ p1(x    ), p2(x + 4), p3(x + 77) })) 
    )

TEST_SIMPLIFY_NUMBER(single_var_15,
    Simplification::NotApplicable()
      .input(    clause({ p1(x +  3), p2(x + -7) }))
    )

TEST_SIMPLIFY_NUMBER(single_var_16,
    Simplification::Success()
      .input(    clause({ r(x + 3, x +  -7) })) 
      .expected( clause({ r(x    , x + -10) })) 
    )

TEST_SIMPLIFY_NUMBER(single_var_17,
    Simplification::Success()
      .input(    clause({ p1(x + (-3)), p2(x + (-7)) })) 
      .expected( clause({ p1(x)       , p2(x + (-4)) })) 
    )
#endif // PHASE >= 3 

TEST_SIMPLIFY_FRACTIONAL(single_var_18,
    Simplification::Success()
      .input(    clause({ p(3 * a * x + 7) })) 
      .expected( clause({ p(x * a + 7) }))
    )

#if PHASE >= 2 
TEST_SIMPLIFY_FRACTIONAL(single_var_19,
    Simplification::Success()
      .input(    clause({ p(3 * a * x + 7 * a) })) 
      .expected( clause({ p(x * a) }))
    )
#endif // PHASE >= 2 

TEST_SIMPLIFY_INTEGER(single_var_power_01,
    Simplification::NotApplicable()
      .input(    clause({ p(x * x * x) }))
    )

TEST_SIMPLIFY_RATIONAL(single_var_power_01,
    Simplification::NotApplicable()
      .input(    clause({ p(x * x * x) }))
    )

TEST_SIMPLIFY_REAL(single_var_power_01,
    Simplification::Success()
      .input(    clause({ p(x * x * x) })) 
      .expected( clause({ p(x)     })) 
    )

TEST_SIMPLIFY_INTEGER(single_var_power_02,
    Simplification::NotApplicable()
      .input(    clause({ p(x * x * x * x) }))
    )

TEST_SIMPLIFY_RATIONAL(single_var_power_02,
    Simplification::NotApplicable()
      .input(    clause({ p(x * x * x * x) }))
    )

TEST_SIMPLIFY_REAL(single_var_power_02,
    Simplification::Success()
      .input(    clause({ p(x * x * x * x) })) 
      .expected( clause({ p(x * x)     })) 
    )

TEST_SIMPLIFY_FRACTIONAL(multi_var_01,
    Simplification::Success()
      .input(    clause({ p(3 * x + 4 * y + 7 * z + 4) }))
      .expected( anyOf(
                    clause({ p(x) }),
                    clause({ p(y) })))
    )

TEST_SIMPLIFY_INTEGER(multi_var_01,
    Simplification::NotApplicable()
      .input(    clause({ p(3 * x + 4 * y + 7 * z + 4) }))
    )

TEST_SIMPLIFY_NUMBER(multi_var_02,
    Simplification::Success()
      .input(    clause({ p(x + 4 * y + 7 * z + 4) }))
      .expected( anyOf(
                    clause({ p(x) }),
                    clause({ p(y) })))
    )

TEST_SIMPLIFY_FRACTIONAL(multi_var_03,
    Simplification::Success()
      .input(    clause({ p1(3 * x + 4 * y + 7 * z + 4), p2(x + 4) }))
      //          ==>    { p1(3 * x +     y + 7 * z + 4), p2(x + 4) }) by (y -> 1/4 y)
      //          ==>    { p1(            y + 7 * z + 4), p2(x + 4) }) by (y -> -3*x + y)
      //          ==>    { p1(            y + 7 * z + 4), p2(x + 4) }) by (y -> -7*z + y)
      //          ==>    { p1(            y            ), p2(x    ) }) by (x -> x - 4)
      .expected( clause({ p1(y),                         p2(x) })) 
    )

TEST_SIMPLIFY_INTEGER(multi_var_03,
    Simplification::NotApplicable()
      .input(    clause({ p1(3 * x + 4 * y + 7 * z + 4), p2(x + 4) }))
    )

TEST_SIMPLIFY_NUMBER(multi_var_04,
    Simplification::Success()
      .input(    clause({ p1(3 * x +     y + 7 * z + 4), p2(x + 4) }))
      //          ==>    { p1(            y + 7 * z + 4), p2(x + 4) }) by (y -> -3*x + y)
      //          ==>    { p1(            y + 7 * z + 4), p2(x + 4) }) by (y -> -7*z + y)
      //          ==>    { p1(            y            ), p2(x    ) }) by (x -> x - 4)
      .expected( clause({ p1(y),                         p2(x) })) 
    )

TEST_SIMPLIFY_FRACTIONAL(multi_var_05,
    Simplification::Success()
      .input(    clause({ p1(3 * x + 2 * y), p2(3 * x + 2 * y) }))
      .expected( anyOf(
                    clause({ p1(x), p2(x) }),
                    clause({ p1(y), p2(y) })))
    )

TEST_SIMPLIFY_INTEGER(multi_var_05,
    Simplification::NotApplicable()
      .input(    clause({ p1(3 * x + 2 * y), p2(3 * x + 2 * y) }))
    )

TEST_SIMPLIFY_FRACTIONAL(multi_var_06,
    Simplification::Success()
      .input(    clause({ p1(3 * x + 2 * y), p2(3 * x + 2 * y + 1) }))
      .expected( anyOf(
                    clause({ p1(x), p2(x + 1) }),
                    clause({ p1(y), p2(y + 1) })
                    ))
    )

TEST_SIMPLIFY_INTEGER(multi_var_06,
    Simplification::NotApplicable()
      .input(    clause({ p1(3 * x + 2 * y), p2(3 * x + 2 * y + 1) }))
    )

TEST_SIMPLIFY_FRACTIONAL(multi_var_07,
    Simplification::Success()
      .input(    clause({ p1(3 * x), p2(3 * x + 2 * y + 1) }))
      .expected( clause({ p1(x)    , p2(y) })) 
    )

TEST_SIMPLIFY_INTEGER(multi_var_07,
    Simplification::NotApplicable()
      .input(    clause({ p1(3 * x), p2(3 * x + 2 * y + 1) }))
    )

TEST_SIMPLIFY_FRACTIONAL(multi_var_08,
    Simplification::Success()
      .input(    clause({ p1(6 * x), p2(6 * x + 2 * y + 2) }))
      //                 { p1(6 * x), p2(        2 * y    ) }  by  y -> -3x + y - 1
      .expected( clause({ p1(    x), p2(            y    ) })) 
    )

#if PHASE >= 2 
TEST_SIMPLIFY_INTEGER(multi_var_08,
    Simplification::Success()
      .input(    clause({ p1(6 * x), p2(6 * x + 2 * y + 2) }))
      //                 { p1(6 * x), p2(        2 * y    ) }  by  y -> -3x + y - 1
      .expected( clause({ p1(6 * x), p2(        2 * y    ) })) 
    )
#endif // PHASE >= 2 

TEST_SIMPLIFY_FRACTIONAL(multi_var_09,
    Simplification::NotApplicable()
      .input(    clause({ p1(x + y), p2(y + z), p3( z + x ) }))
    )

TEST_SIMPLIFY_FRACTIONAL(multi_var_10,
    Simplification::Success()
      .input(    clause({ p1(x + y + 1), p2(y + 1 + z), p3( z + x ) }))
      .expected( clause({ p1(x + y    ), p2(y     + z), p3( z + x ) }))
    )

TEST_SIMPLIFY_FRACTIONAL(multi_var_11,
    Simplification::Success()
      .input(    clause({ p1(2 * x + 3 * y), p2(3 * y + 4 * z), p3( 4 * z + 2 * x ) }))
      .expected( clause({ p1(    x +     y), p2(    y +     z), p3(     z +     x ) }))
    )

TEST_SIMPLIFY_FRACTIONAL(multi_var_12,
    Simplification::Success()
      .input(    clause({ p1(x + y + 2 * z), p2(x + y + z) }))
      //   =====> clause({ p1(x     + 2 * z), p2(x     + z) }), 
      .expected( anyOf(
                    clause({ p1(x + 2 * z), p2(x + z) }), 
                    clause({ p1(y + 2 * z), p2(y + z) })))
    )


TEST_SIMPLIFY_FRACTIONAL(multi_var_13,
    Simplification::Success()
      .input(    clause({ p1(x + y + 1), p2(x + y + 2), p3(x + y + z) }))
      //   =====> clause({ p1(x     + 1), p2(x     + 2), p3(x     + z) }), 
      .expected( anyOf(
                    clause({ p1(x + 1), p2(x + 2), p3(        z) }), 
                    clause({ p1(y + 1), p2(y + 2), p3(        z) })))
    )

TEST_SIMPLIFY_FRACTIONAL(multi_var_14,
    Simplification::Success()
      .input(    clause({ p1(x + y + 1), p2(x + y + 2), p3(x + y + z), p3(y + z + 1) }))
      //    ====> clause({ p1(x + y + 1), p2(x + y + 2), p3(x +     z), p3(    z + 1) }),
      //    ====> clause({ p1(    y + 1), p2(    y + 2), p3(x +     z), p3(    z + 1) }),
      //    ====> clause({ p1(    y + 1), p2(    y + 2), p3(x        ), p3(    z + 1) }),
      //    ====> clause({ p1(    y + 1), p2(    y + 2), p3(x        ), p3(    z    ) }),
      
      .expected( anyOf(
                      clause({ p1(    x + 1), p2(    x + 2), p3(y        ), p3(    z    ) }),
                      clause({ p1(    y + 1), p2(    y + 2), p3(x        ), p3(    z    ) })
                      )) 
    )

TEST_SIMPLIFY_FRACTIONAL(multi_var_15,
    Simplification::Success()
      .input(    clause({ p1(x + y + 1), p2(x + y + 1) })) 
      .expected( anyOf(
                     clause({ p1(x), p2(x) }),
                     clause({ p1(y), p2(y) })))
    )

TEST_SIMPLIFY_FRACTIONAL(multi_var_16,
    Simplification::Success()
      .input(    clause({ p1(x + y + 1), p2(x     + 1) })) 
      .expected( clause({ p1(y)        , p2(x) }))
    )

TEST_SIMPLIFY_FRACTIONAL(multi_var_18,
    Simplification::NotApplicable()
      .input(    clause({ p(3 * x + f(x)) }))
    )

TEST_SIMPLIFY_FRACTIONAL(multi_var_19,
    Simplification::Success()
      .input(    clause({ p(3 * x + f(3 * x)) }))
      .expected( clause({ p(x + f(x)) })) 
    )

TEST_SIMPLIFY_NUMBER(complex_expressions_01,
    Simplification::Success()
      .input(    clause({ p(-1 * x + f(-1 * x)) }))
      .expected( clause({ p(x + f(x)) })) 
    )

TEST_SIMPLIFY_FRACTIONAL(complex_expressions_02,
    Simplification::Success()
      .input(    clause({ p(3 * x * f(3 * y)) }))
      .expected( clause({ p(x * f(y)) })) 
    )

TEST_SIMPLIFY_FRACTIONAL(fallancy_01,
    Simplification::Success()
      .input(    clause({ p(3 * x * y) }))
      .expected( anyOf(
                       clause({ p(x) }), 
                       clause({ p(y) }))) 
    )

TEST_SIMPLIFY_FRACTIONAL(fallancy_02,
    Simplification::Success()
      .input(    clause({ p1(3 * x * y), p2(3 * x * f(y)) }))
      .expected( clause({ p1(    x * y), p2(    x * f(y)) })) 
    )

TEST_SIMPLIFY_FRACTIONAL(fallancy_03,
    Simplification::Success()
      .input(    clause({ p1(x * y), p2(x * y + 1) }))
      .expected( anyOf(
                      clause({ p1(x), p2(x + 1) }), 
                      clause({ p1(y), p2(y + 1) })
                    ))
    )

#if PHASE >= 3
TEST_SIMPLIFY_FRACTIONAL(fallancy_04,
    Simplification::Success()
      .input(    clause({ p1(6 * x * y), p2(3 * x), p3(2 * y) }))
      .expected( clause({ p1(    x * y), p2(    x), p3(    y) })) 
    )
#endif // PHASE >= 3

TEST_SIMPLIFY_FRACTIONAL(fallancy_05,
    Simplification::Success()
      .input(    clause({ p1(2 * x * y), p2(2 * x), p3(2 * y) }))
      .expected( anyOf(
                    clause({ p1(    x * y), p2(    x), p3(2 * y) }),
                    clause({ p1(    x * y), p2(2 * x), p3(    y) }))) 
    )

TEST_SIMPLIFY_FRACTIONAL(fallancy_06,
    Simplification::NotApplicable()
      .input(    clause({ p1(2 * x + x * x), p2(2 * x) }))
    )

TEST_SIMPLIFY_FRACTIONAL(fallancy_07,
    Simplification::Success()
      .input(    clause({ p1(x + f(3 + y)) }))
      .expected( clause({ p1(x           ) })) 
    )

TEST_SIMPLIFY_FRACTIONAL(fallancy_08,
    Simplification::Success()
      .input(    clause({ p1(f(3 + x) + f(3 + y)) })) 
      .expected( clause({ p1(f(    x) + f(    y)) }))
    )

TEST_SIMPLIFY_NUMBER(generalize_var_1,
    Simplification::Success()
      .input(    clause({ p1(f(x * y * z) + f(x * y)) })) 
      //  ======> clause({ p1(f(x     * z) + f(x    )) }), 
      .expected( anyOf(
          clause({ p1(f(x * z) + f(x)) }),
          clause({ p1(f(y * z) + f(y)) })
          ))
    )

TEST_SIMPLIFY_NUMBER(generalize_var_2,
    Simplification::Success()
      .input(    clause({ p1(x * y + f(x * y * z) + f(x * y)) })) 
      //   =====> clause({ p1(x     + f(x     * z) + f(x    )) }), 
      .expected( anyOf(
                       clause({ p1(x + f(x * z) + f(x)) }),
                       clause({ p1(y + f(y * z) + f(y)) })
                       )) 
    )

TEST_SIMPLIFY_NUMBER(generalize_var_3,
    Simplification::NotApplicable()
      .input(    clause({ p1(x * y + f(y)) }))
    )

TEST_SIMPLIFY_NUMBER(generalize_var_4,
    Simplification::Success()
      .input(    clause({ p1(x * x * y) })) 
      .expected( anyOf(
                       clause({ p1(y) }),
                       clause({ p1(x) })
                       )) 
    )

TEST_SIMPLIFY_NUMBER(generalize_var_5,
    Simplification::NotApplicable()
      .input(    clause({ p1(x * x * y), p2(x * y) }))
    )

TEST_SIMPLIFY_NUMBER(generalize_var_6,
    Simplification::Success()
      .input(    clause({ p1(x * x * y), p2(z * x * x * y) })) 
      .expected( anyOf(
                       clause({ p1(x), p2(x * z) }),
                       clause({ p1(y), p2(y * z) })
                      )) 
    )

TEST_SIMPLIFY_NUMBER(generalize_var_7,
    Simplification::Success()
      .input(    clause({ p1(x * x * y * z), p2(z * x * x * x * y) })) 
      .expected( anyOf(
                       clause({ p1(x * x * z), p2(x * x * x * z) }),
                       clause({ p1(x * x * y), p2(x * x * x * y) })
                      )) 
    )

TEST_SIMPLIFY_NUMBER(generalize_var_8,
    Simplification::Success()
      .input(    clause({ p1(( x * x ) * ( y ) * ( z * z )), p2(( x * x * x ) * ( y ) * (z * z)) })) 
      .expected( anyOf(
                       clause({ p1(( x * x ) * z), p2(( x * x * x ) * z) }),
                       clause({ p1(( x * x ) * y), p2(( x * x * x ) * y) })
                      )) 
    )

TEST_SIMPLIFY_REAL(generalize_var_9,
    Simplification::Success()
      .input(    clause({ p1(( x * x ) * ( z * z * z )), p2(( x * x * x ) * (z * z * z)) })) 
      //   =====> clause({ p1(( x * x ) * (     z     )), p2(( x * x * x ) * (    z    )) }), 
      .expected( anyOf(
                  clause({ p1(( x * x ) *       z      ), p2(( x * x * x ) *      z     ) })
          ))
    )

TEST_SIMPLIFY_RATIONAL(generalize_var_9,
    Simplification::NotApplicable()
      .input(    clause({ p1(( x * x ) * ( z * z )), p2(( x * x * x ) * (z * z)) }))
    )

TEST_SIMPLIFY_INTEGER(generalize_var_9,
    Simplification::NotApplicable()
      .input(    clause({ p1(( x * x ) * ( z * z )), p2(( x * x * x ) * (z * z)) }))
    )

TEST_SIMPLIFY_REAL(generalize_power_1,
    Simplification::NotApplicable()
      .input(    clause({ p1(x * x * x + f(x * x)) }))
    )

TEST_SIMPLIFY_REAL(generalize_power_2,
    Simplification::Success()
      .input(    clause({ p1(x * x * x + f(x * x * x)) })) 
      .expected( clause({ p1(x + f(x)) })) 
    )

TEST_SIMPLIFY_REAL(generalize_power_3,
    Simplification::Success()
      .input(    clause({ p1(x * x * x + f(y * y * y)) })) 
      .expected( clause({ p1(x) })) 
    )

TEST_SIMPLIFY_REAL(generalize_power_4,
    Simplification::NotApplicable()
      .input(    clause({ x * x >= 0 }))
    )

TEST_SIMPLIFY_REAL(generalize_power_5,
    Simplification::Success()
      .input(    clause({ p1(x * x * x + y * y), p2( y + a ) })) 
      .expected( clause({ p1(x), p2(y) })) 
    )

TEST_SIMPLIFY_REAL(bug_01,
    Simplification::NotApplicable()
      .input(    clause({ x * (y + z) == x * y + x * z }))
    )

TEST_SIMPLIFY_NUMBER(bug_02,
    Simplification::NotApplicable()
      .input(    clause({ ((x+(1*x)) + ((1*y)+y)) == (2*(x+y))}))
    )

// TODO: what about { y = 0 \/ p(y*x) } ===> { p(x) }
// TODO: what about { p(f * x) } ===> { p(x) } if f isNonZero
// TODO: what about { p(f * x) } ===> { p(0) } if f isZero
// TODO: what about { p(t * x * x) } ===> { p(x) } for REALS only

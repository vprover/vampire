/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#include "Inferences/ALASCA/Normalization.hpp"
#include "Inferences/ALASCA/TautologyDeletion.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Inferences/LfpRule.hpp"

#include "Test/SimplificationTester.hpp"

using namespace std;
using namespace Kernel;
using namespace Inferences;
using namespace Test;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// TEST UNIT INITIALIZATION
/////////////////////////////////////

namespace {

#define MY_SIMPL_RULE LfpISE<TupleISE<ALASCA::Normalization, ALASCA::TautologyDeletion>>
#define MY_SIMPL_TESTER Simplification::SimplificationTester
#define MY_SYNTAX_SUGAR                                                                   \
  NUMBER_SUGAR(Real)                                                                      \
  DECL_DEFAULT_VARS                                                                       \
  DECL_CONST(a, Real)                                                                     \
  DECL_CONST(b, Real)                                                                     \
  DECL_CONST(c, Real)                                                                     \
  DECL_FUNC(f, {Real}, Real)                                                              \
  DECL_PRED(p, {Real})                                                                    \
  DECL_PRED(q, {Real})                                                                    \

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// TEST CASES
/////////////////////////////////////

TEST_SIMPLIFY_WITH_SATURATION(taut_del_1,
    Simplification::Success()
      .input(    clause({  x > 0, -x >= 0   }))
      .expected( Simplification::Redundant {} )
    )

TEST_SIMPLIFY_WITH_SATURATION(taut_del_2,
    Simplification::Success()
      .input(    clause({  -a + b > 0, a - b >= 0   }))
      .expected( Simplification::Redundant {} )
    )

TEST_SIMPLIFY_WITH_SATURATION(taut_del_3,
    Simplification::Success()
      .input(    clause({  -a + b == 0, a - b != 0   }))
      .expected( Simplification::Redundant {} )
    )

}
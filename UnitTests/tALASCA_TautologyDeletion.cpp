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
#include "Inferences/InferenceEngine.hpp"
#include "Kernel/ALASCA/State.hpp"
#include "Test/UnitTesting.hpp"
#include "Test/TestUtils.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Inferences/GaussianVariableElimination.hpp"

#include "Test/SyntaxSugar.hpp"
#include "Test/TestUtils.hpp"
#include "Test/SimplificationTester.hpp"

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
template<class Rule>
class AlascaSimplTester : public Test::Simplification::SimplificationTester
{
  std::shared_ptr<AlascaState> _state;
  LfpISE<TupleISE<ALASCA::Normalization, Rule>> _rule;
public:
  AlascaSimplTester()
    : _state(testAlascaState())
    , _rule(lfpISE(tupleISE(ALASCA::Normalization(_state), Rule(_state))))
  { }

  virtual Kernel::Clause* simplify(Kernel::Clause* in) override 
  { return _rule.simplify(in); }

  virtual bool eq(Kernel::Clause* lhs, Kernel::Clause* rhs) const override
  {
    return TestUtils::eqModAC(lhs, rhs);
  }
};

REGISTER_SIMPL_TESTER(AlascaSimplTester<ALASCA::TautologyDeletion>)

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

TEST_SIMPLIFY(taut_del_1,
    Simplification::Success()
      .input(    clause({  x > 0, -x >= 0   }))
      .expected( Simplification::Redundant {} )
    )

TEST_SIMPLIFY(taut_del_2,
    Simplification::Success()
      .input(    clause({  -a + b > 0, a - b >= 0   }))
      .expected( Simplification::Redundant {} )
    )

TEST_SIMPLIFY(taut_del_3,
    Simplification::Success()
      .input(    clause({  -a + b == 0, a - b != 0   }))
      .expected( Simplification::Redundant {} )
    )

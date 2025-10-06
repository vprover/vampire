/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#include "Inferences/ALASCA/InequalityFactoring.hpp"
#include "Inferences/ALASCA/Normalization.hpp"
#include "Inferences/ALASCA/TautologyDeletion.hpp"
#include "Inferences/InferenceEngine.hpp"
#include "Kernel/ALASCA/State.hpp"
#include "Test/TestUtils.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Inferences/GaussianVariableElimination.hpp"

#include "Test/SyntaxSugar.hpp"
#include "Test/TestUtils.hpp"
// #include "Test/SimplificationManyTester.hpp"
//
// using namespace std;
// using namespace Kernel;
// using namespace Inferences;
// using namespace Test;
//
// ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// ////// TEST UNIT INITIALIZATION
// /////////////////////////////////////
//
//
// /** 
//  * NECESSARY: We need a subclass of SimplificationTester
//  */
// template<class Rule>
// class AlascaSimplManyTester : public Test::SimplificationMany::SimplificationManyTester
// {
//   std::shared_ptr<AlascaState> _state;
//   ALASCA::Normalization _norm;
//   Rule _rule;
// public:
//   AlascaSimplManyTester()
//     : _state(testAlascaState())
//     , _norm(ALASCA::Normalization(_state))
//     , _rule(Rule(_state))
//   { }
//
//   virtual Kernel::Clause* normalize(Kernel::Clause* in) override 
//   { return _norm.simplify(in); }
//
//   virtual Kernel::ClauseIterator simplifyMany(Kernel::Clause* in) override 
//   { return _rule.simplifyMany(in); }
// };
//
// REGISTER_SIMPL_TESTER(AlascaSimplManyTester<ALASCA::InequalityFactoringDemod>)
//
// #define MY_SYNTAX_SUGAR                                                                   \
//   NUMBER_SUGAR(Real)                                                                      \
//   DECL_DEFAULT_VARS                                                                       \
//   DECL_CONST(a, Real)                                                                     \
//   DECL_CONST(b, Real)                                                                     \
//   DECL_CONST(c, Real)                                                                     \
//   DECL_FUNC(f, {Real}, Real)                                                              \
//   DECL_FUNC(f2, {Real,Real}, Real)                                                              \
//   DECL_PRED(p, {Real})                                                                    \
//   DECL_PRED(q, {Real})                                                                    \
//
// ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// ////// TEST CASES
// /////////////////////////////////////
//
// TEST_SIMPLIFY(simple1,
//     SimplificationMany::Success()
//       .input(    clause({  a > 0, a + b > 0   }))
//       .expected( exactly(
//           clause({ 0 > b, a + b > 0 }), 
//           clause({ b > 0, a > 0 }) ))
//     )
//
// TEST_SIMPLIFY(bug1,
//     SimplificationMany::Success()
//       .input(    clause({  x - y > 0, x - y - f2(x, y) >= 0   }))
//       .expected( exactly(
//           clause({ -(-f2(x,y)) >  0, x + -y + -f2(x,y) >= 0 }),
//           clause({   -f2(x,y)  >= 0, x + -y            >  0 })
//           ))
//     )
//
// TEST_SIMPLIFY(bug2,
//     SimplificationMany::Success()
//       .input(    clause({  x - a >= 0, -a - f(x) >= 0, -x -f(x) >= 0   }))
//       .expected( exactly(
//           clause({ x + -a >= 0, -x + a > 0, -a + -f(x) >= 0 }), 
//           clause({ x + -a >= 0, x + -a > 0, -x + -f(x) >= 0 })
//           // clause({ -(-f2(x,y)) >  0, x + -y + -f2(x,y) >= 0 }),
//           // clause({   -f2(x,y)  >= 0, x + -y            >  0 })
//           ))
//     )

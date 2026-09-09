/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __TEST__TRANSFORMATION_TESTER_HPP__
#define __TEST__TRANSFORMATION_TESTER_HPP__

/**
 * This file provides macros and classes used to write nice tests for formula transformation rules.
 *
 * \see UnitTests/tPreprocess_CNF.cpp, for usage a example
 *
 * Don't rely on any part of the interface, but the things contained in the examples,
 * because it's rather unstable.
 */

#include "Debug/Assertion.hpp"
#include "Forwards.hpp"

#include "Kernel/Problem.hpp"
#include "Lib/Environment.hpp"

#include "Test/BuilderPattern.hpp"
#include "Test/TestUtils.hpp"
#include "UnitTesting.hpp"

namespace Test {

namespace Transformation {

inline bool deepEq(VSList* v1, VSList* v2) {
  return iterTraits(v1->iter()).zip(v2->iter()).all([](auto p){ return p.first == p.second; });
}

inline bool deepEq(Formula* f1, Formula* f2) {
  if (f1->connective() != f2->connective()) {
    return false;
  }
  switch (f1->connective()) {
    case Connective::LITERAL:
      return f1->literal() == f2->literal();
    case Connective::NOT:
      return deepEq(static_cast<NegatedFormula*>(f1)->subformula(), static_cast<NegatedFormula*>(f2)->subformula());
    case Connective::AND:
    case Connective::OR:
      return iterTraits(static_cast<JunctionFormula*>(f1)->getArgs()->iter())
        .zip(static_cast<JunctionFormula*>(f2)->getArgs()->iter())
        .all([](auto p) { return deepEq(p.first, p.second); });
    case Connective::IMP:
    case Connective::IFF:
    case Connective::XOR:
      return deepEq(static_cast<BinaryFormula*>(f1)->lhs(), static_cast<BinaryFormula*>(f2)->lhs()) &&
        deepEq(static_cast<BinaryFormula*>(f1)->rhs(), static_cast<BinaryFormula*>(f2)->rhs());
    case Connective::FORALL:
    case Connective::EXISTS:
      return deepEq(static_cast<QuantifiedFormula*>(f1)->varList(), static_cast<QuantifiedFormula*>(f2)->varList()) &&
        deepEq(static_cast<QuantifiedFormula*>(f1)->subformula(), static_cast<QuantifiedFormula*>(f2)->subformula());
    default:
      ASSERTION_VIOLATION_REP(f1->toString());
  }
}

inline bool deepEq(Unit* u1, Unit* u2) {
  if (u1->isClause() != u2->isClause()) {
    return false;
  }
  if (u1->isClause()) {
    return TestUtils::eqModAC(u1->asClause(), u2->asClause());
  }
  return deepEq(u1->getFormula(), u2->getFormula());
}

class TransformationTest
{
public:

  __BUILDER_METHOD(TransformationTest, UnitStack, input)
  __BUILDER_METHOD(TransformationTest, UnitStack, expected)

  template<typename Rule>
  void run() {

    Problem p(UnitList::fromIterator(_input.iter()));
    env.setMainProblem(&p);

    Rule::apply(p);

    UnitStack actual = UnitStack::fromIterator(p.units()->iter());
    if (!TestUtils::permEq(actual, _expected, [&](auto act, auto exp) { return deepEq(act, exp); })) {
      std::cout << "[  actual  ]: " << pretty(actual) << std::endl;
      std::cout << "[ expected ]: " << pretty(_expected) << std::endl;
      ASSERTION_VIOLATION;
    }
  }
};

#define TEST_TRANSFORMATION(name, ...)                                                    \
  TEST_TRANSFORMATION_WITH_SUGAR(name, MY_TRAFO_RULE, MY_SYNTAX_SUGAR, __VA_ARGS__) 

#define TEST_TRANSFORMATION_WITH_SUGAR(name, rule, syntax_sugar, test)                    \
  TEST_FUN(name) {                                                                        \
    __ALLOW_UNUSED(syntax_sugar)                                                          \
    test.run<rule>();                                                                     \
  }                                                                                       \

} // namespace Transformation

} // namespace Test

#endif // __TEST__TRANSFORMATION_TESTER_HPP__

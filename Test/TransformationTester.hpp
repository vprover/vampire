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

#include "Kernel/Clause.hpp"
#include "Kernel/Problem.hpp"

#include "Test/BuilderPattern.hpp"
#include "UnitTesting.hpp"

namespace Test {

namespace Transformation {

inline bool deepEq(Clause* c1, Clause* c2) {
  if (c1->length() != c2->length()) {
    return false;
  }
  for (unsigned i = 0; i < c1->length(); i++) {
    if ((*c1)[i] != (*c2)[i]) {
      return false;
    }
  }
  return true;
}

inline bool deepEq(Formula* f1, Formula* f2) {
  if (f1->connective() != f2->connective()) {
    return false;
  }
  switch (f1->connective()) {
    case LITERAL:
      return f1->literal() == f2->literal();
    default:
      ASSERTION_VIOLATION;
  }
}

inline bool deepEq(Unit* u1, Unit* u2) {
  if (u1->isClause() != u2->isClause()) {
    return false;
  }
  if (u1->isClause()) {
    return deepEq(u1->asClause(), u2->asClause());
  }
  return deepEq(u1->getFormula(), u2->getFormula());
}

class TransformationTest
{
public:

  __BUILDER_METHOD(TransformationTest, Stack<Unit*>, input)
  __BUILDER_METHOD(TransformationTest, Stack<Unit*>, expected)

  template<typename Rule>
  void run() {

    Problem p(UnitList::fromIterator(_input.iter()));

    Rule rule;
    rule.apply(p);

    auto actual = p.units();
    auto expI = 0;
    while (actual) {
      ASS_REP(expI < _expected.size(), "unexpected unit " + actual->head()->toString());

      if (!deepEq(actual->head(), _expected[expI])) {
        std::cout << "unit mismatch" << std::endl;
        std::cout << "[  actual  ]: " << *actual->head() << std::endl;
        std::cout << "[ expected ]: " << *_expected[expI] << std::endl;
        ASSERTION_VIOLATION;
      }
      expI++;
      actual = actual->tail();
    }
    ASS_REP(expI == _expected.size(), "expected unit " + _expected[expI]->toString());
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

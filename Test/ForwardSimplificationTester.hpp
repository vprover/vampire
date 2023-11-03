/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __TEST__FORWARD_SIMPLIFICATION_TESTER_HPP__
#define __TEST__FORWARD_SIMPLIFICATION_TESTER_HPP__

/**
 * This file provides macros and classes used to write nice tests for simplification rules.
 *
 * Check out UnitTests/tGaussianElimination.cpp, to see how it is to be used.
 */

#include "Test/TestUtils.hpp"
#include "Test/ClausePattern.hpp"
#include "Test/MockedSaturationAlgorithm.hpp"

#include "Kernel/Clause.hpp"
#include "Lib/Coproduct.hpp"

using namespace Inferences;
using namespace Kernel;

namespace Test {

namespace ForwardSimplification {

struct EqualityOp {
  virtual bool eq(Clause const* lhs, Clause const* rhs) const
  {
    if (!lhs || !rhs) { return lhs == rhs; }
    return TestUtils::eqModAC(lhs, rhs);
  }
};

class TestCase
{
  Kernel::Clause* _input;
  Option<ClausePattern> _expected;
  Stack<Clause*> _context;
  ForwardSimplificationEngine* _rule;
  std::function<Stack<Indexing::Index*>(const Ordering&, const Options&)> _indices;

public:
  TestCase() : _input(nullptr), _expected(), _context(), _rule(), _indices() {}

#define BUILDER_METHOD(type, field)                                                                           \
  TestCase field(type field)                                                                                  \
  {                                                                                                           \
    this->_##field = decltype(_##field)(std::move(field));                                                    \
    return *this;                                                                                             \
  }                                                                                                           \

  BUILDER_METHOD(Clause*, input)
  BUILDER_METHOD(ClausePattern, expected)
  BUILDER_METHOD(Stack<Clause*>, context)
  BUILDER_METHOD(ForwardSimplificationEngine*, rule)
  BUILDER_METHOD(std::function<Stack<Indexing::Index*>(const Ordering&, const Options&)>, indices)

  void run() {

    // set up saturation algorithm
    auto container = PlainClauseContainer();
    Problem p;
    auto units = UnitList::singleton(_input);
    p.addUnits(units);
    Options o;
    env.setMainProblem(&p);
    MockedSaturationAlgorithm alg(p, o);
    KBO kbo(p,o);
    Ordering::trySetGlobalOrdering(SmartPtr<Ordering>(&kbo, true));

    auto ind = _indices(kbo,o);
    _rule->setTestIndices(ind);
    _rule->InferenceEngine::attach(&alg);
    for (auto i : ind) {
      i->attachContainer(&container);
    }

    // add the clauses to the index
    for (auto c : _context) {
      c->setStore(Clause::ACTIVE);
      container.add(c);
    }

    Clause* replacement = nullptr;
    ClauseIterator premises;
    auto res = _rule->perform(_input, replacement, premises);
    EqualityOp eqOp;

    if (!res) {
      std::cout  << std::endl;
      std::cout << "[     case ]: " << pretty(*_input) << std::endl;
      std::cout << "[ expected ]: " << pretty(_expected) << std::endl;
      std::cout << "[not performed]" << std::endl;
      exit(-1);
    }
    if (!_expected.unwrap().matches(eqOp,replacement)) {
      std::cout  << std::endl;
      std::cout << "[     case ]: " << pretty(*_input) << std::endl;
      std::cout << "[       is ]: " << pretty(replacement) << std::endl;
      std::cout << "[ expected ]: " << pretty(_expected) << std::endl;
      exit(-1);
    }
  }
};

#define TEST_FW_SIMPLIFY(name, ...)                                                                           \
        TEST_FW_SIMPLIFY_WITH_SUGAR(name, MY_SYNTAX_SUGAR, __VA_ARGS__)

#define TEST_FW_SIMPLIFY_WITH_SUGAR(name, syntax_sugar, ...)                                                  \
  TEST_FUN(name) {                                                                                            \
    __ALLOW_UNUSED(syntax_sugar)                                                                              \
    __VA_ARGS__.run();                                                                                   \
  }                                                                                                           \

} // namespace ForwardSimplification

} // namespace Test

#endif // __TEST__FORWARD_SIMPLIFICATION_TESTER_HPP__

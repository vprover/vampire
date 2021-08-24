/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __TEST__GENERATION_TESTER_HPP__
#define __TEST__GENERATION_TESTER_HPP__

/**
 * This file provides macros and classes used to write nice tests for generating inference rules.
 *
 * \see UnitTests/tEqualityResolution.cpp, for usage a example
 *
 * Don't rely on any part of the interface, but the things containted in the examples,
 * because it's rather unstable.
 */

#include "Test/TestUtils.hpp"
#include "Kernel/Clause.hpp"
#include "Lib/Coproduct.hpp"
#include "Test/ClausePattern.hpp"
#include "Saturation/Otter.hpp"
#include "Kernel/Problem.hpp"
#include "Shell/Options.hpp"
#include "Test/MockedSaturationAlgorithm.hpp"
#include "Test/SyntaxSugar.hpp"

namespace Test {

template<class... As>
Stack<ClausePattern> exactly(As... as) 
{
  Stack<ClausePattern> out { as... };
  return out;
}

namespace Generation {
class TestCase;

template<class Rule>
class GenerationTester
{
  Rule* _rule;

public:

  GenerationTester(Rule* rule)
    : _rule(rule)
  {}

  ~GenerationTester()
  {
    delete _rule;
  }

  virtual bool eq(Kernel::Clause const* lhs, Kernel::Clause const* rhs) const 
  { return TestUtils::eqModAC(lhs, rhs); }

  friend class TestCase;
};

class TestCase
{
  using Clause = Kernel::Clause;
  Option<SimplifyingGeneratingInference*> _rule;
  Clause* _input;
  Stack<ClausePattern> _expected;
  Stack<Clause*> _context;
  bool _premiseRedundant;
  Stack<Indexing::Index*> _indices;

  template<class Is, class Expected>
  void testFail(Is const& is, Expected const& expected) {
      cout  << endl;
      cout << "[  context ]: " << pretty(_context) << endl;
      cout << "[     case ]: " << pretty(*_input) << endl;
      cout << "[       is ]: " << pretty(is) << endl;
      cout << "[ expected ]: " << pretty(expected) << endl;
      exit(-1);
  }

public:

  TestCase() : _rule(), _input(NULL), _expected(), _premiseRedundant(false) {}

#define BUILDER_METHOD(type, field)                                                                           \
  TestCase field(type field)                                                                                  \
  {                                                                                                           \
    this->_##field = decltype(_##field)(std::move(field));                                                    \
    return *this;                                                                                             \
  }                                                                                                           \

  BUILDER_METHOD(Clause*, input)
  BUILDER_METHOD(Stack<Clause*>, context)
  BUILDER_METHOD(Stack<ClausePattern>, expected)
  BUILDER_METHOD(bool, premiseRedundant)
  BUILDER_METHOD(SimplifyingGeneratingInference*, rule)
  BUILDER_METHOD(Stack<Indexing::Index*>, indices)

  template<class Rule>
  void run(GenerationTester<Rule>& simpl) {

    // set up clause container and indexing strucure
    auto container = PlainClauseContainer();
    SimplifyingGeneratingInference* rule = _rule.unwrapOrElse([&](){ return simpl._rule; });
    rule->setTestIndices(_indices);
    for (auto i : _indices) {
      i->attachContainer(&container);
    }

    // add the clauses to the index
    for (auto c : _context) {
      container.add(c);
    }

    // run rule
    auto res = rule->generateSimplify(_input);

    // run checks
    auto& sExp = this->_expected;
    auto  sRes = Stack<Kernel::Clause*>::fromIterator(res.clauses);

    if (!TestUtils::permEq(sExp, sRes, [&](auto exp, auto res) { return exp.matches(simpl, res); })) {
      testFail(sRes, sExp);
    }

    if (_premiseRedundant != res.premiseRedundant) {
      auto wrapStr = [](bool b) -> vstring { return b ? "premise is redundant" : "premis not redundant"; };
      testFail( wrapStr(res.premiseRedundant), wrapStr(_premiseRedundant));
    }
  }
};

#define __CREATE_GEN_TESTER CAT(__createGenTester_, UNIT_ID)

#define REGISTER_GEN_TESTER(t, ...) auto __CREATE_GEN_TESTER() { return Test::Generation::GenerationTester<t>(new t(__VA_ARGS__)); }

#define TEST_GENERATION(name, ...)                                                                            \
        TEST_GENERATION_WITH_SUGAR(name, MY_SYNTAX_SUGAR, __VA_ARGS__) 

#define TEST_GENERATION_WITH_SUGAR(name, syntax_sugar, ...)                                                   \
  TEST_FUN(name) {                                                                                            \
    auto tester = __CREATE_GEN_TESTER();                                                                      \
    __ALLOW_UNUSED(syntax_sugar)                                                                              \
    auto test = __VA_ARGS__;                                                                                  \
    test.run(tester);                                                                                         \
  }                                                                                                           \

} // namespace Simplification

} // namespace Test

#endif // __TEST__GENERATION_TESTER_HPP__

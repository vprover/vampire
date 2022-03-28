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

inline Stack<ClausePattern> none() {
  return Stack<ClausePattern>();
}

namespace Generation {
class TestCase;

template<class Rule>
class GenerationTester
{
  Rule _rule;

public:
  GenerationTester()
    : _rule()
  {}

  virtual bool eq(Kernel::Clause const* lhs, Kernel::Clause const* rhs)
  { return TestUtils::eqModAC(lhs, rhs); }

  friend class TestCase;
};

class TestCase
{
  using Clause = Kernel::Clause;
  using OptionMap = Stack<pair<vstring,vstring>>;
  Option<SimplifyingGeneratingInference*> _rule;
  Clause* _input;
  Stack<ClausePattern> _expected;
  Stack<Clause*> _context;
  bool _premiseRedundant;
  Stack<Indexing::Index*> _indices;
  OptionMap _options;

  template<class Is, class Expected>
  void testFail(Is const& is, Expected const& expected) {
      cout  << endl;
      cout << "[  context ]: " << pretty(_context) << endl;
      cout << "[  options ]: " << pretty(_options) << endl;
      cout << "[     case ]: " << pretty(*_input) << endl;
      cout << "[       is ]: " << pretty(is) << endl;
      cout << "[ expected ]: " << pretty(expected) << endl;
      exit(-1);
  }

public:

  TestCase() : _rule(), _input(NULL), _expected(), _premiseRedundant(false), _options() {}

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
  BUILDER_METHOD(OptionMap, options)

  template<class Rule>
  void run(GenerationTester<Rule>& simpl) {

    // set up saturation algorithm
    auto container = PlainClauseContainer();
    Problem p;
    Options o;
    for (const auto& kv : _options) {
      o.set(kv.first, kv.second);
      env.options->set(kv.first, kv.second);
    }
    MockedSaturationAlgorithm alg(p, o);
    SimplifyingGeneratingInference& rule = *_rule.unwrapOrElse([&](){ return &simpl._rule; });
    rule.setTestIndices(_indices);
    rule.InferenceEngine::attach(&alg);
    for (auto i : _indices) {
      i->attachContainer(&container);
    }

    // add the clauses to the index
    for (auto c : _context) {
      c->setStore(Clause::ACTIVE);
      container.add(c);
    }

    // run rule
    _input->setStore(Clause::ACTIVE);
    auto res = rule.generateSimplify(_input);

    // run checks
    auto& sExp = this->_expected;
    auto  sRes = Stack<Kernel::Clause*>::fromIterator(res.clauses);

    if (!TestUtils::permEq(sExp, sRes, [&](auto exp, auto res) { return exp.matches(simpl, res); })) {
      testFail(sRes, sExp);
    }

    if (_premiseRedundant != res.premiseRedundant) {
      auto wrapStr = [](bool b) -> vstring { return b ? "premise is redundant" : "premise is not redundant"; };
      testFail( wrapStr(res.premiseRedundant), wrapStr(_premiseRedundant));
    }

    // tear down saturation algorithm
    rule.InferenceEngine::detach();
  }
};

#define __CREATE_GEN_TESTER CAT(__createGenTester_, UNIT_ID)

#define REGISTER_GEN_TESTER(t, ...) auto __CREATE_GEN_TESTER() { return Test::Generation::GenerationTester<t>(); }

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

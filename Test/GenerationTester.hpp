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

#define TEST_FN_ASS_EQ(VAL1, VAL2)                         \
  [] (std::string& s1, std::string& s2) {                          \
    bool res = (VAL1 == VAL2);                             \
    if (!res) {                                            \
      s1 = Lib::Int::toString(VAL1);                            \
      s1.append(" != ");                                   \
      s1.append(Int::toString(VAL2));                      \
      s2 = std::string(#VAL1);                                 \
      s2.append(" == ");                                   \
      s2.append(#VAL2);                                    \
    }                                                      \
    return res;                                            \
  }

template<class... As>
Lib::Stack<ClausePattern> exactly(As... as) 
{
  Lib::Stack<ClausePattern> out { as... };
  return out;
}

inline Lib::Stack<ClausePattern> none() {
  return Lib::Stack<ClausePattern>();
}

namespace Generation {
class TestCase;

template<class Rule>
class GenerationTester
{
protected:
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
  using OptionMap = Lib::Stack<std::pair<std::string,std::string>>;
  using Condition = std::function<bool(std::string&, std::string&)>;
  Lib::Option<SimplifyingGeneratingInference*> _rule;
  Clause* _input;
  Lib::Stack<ClausePattern> _expected;
  Lib::Stack<Clause*> _context;
  bool _premiseRedundant;
  Lib::Stack<Indexing::Index*> _indices;
  std::function<void(SaturationAlgorithm&)> _setup = [](SaturationAlgorithm&){};
  OptionMap _options;
  Lib::Stack<Condition> _preConditions;
  Lib::Stack<Condition> _postConditions;

  template<class Is, class Expected>
  void testFail(Is const& is, Expected const& expected) {
      std::cout  << std::endl;
      std::cout << "[  context ]: " << pretty(_context) << std::endl;
      std::cout << "[  options ]: " << pretty(_options) << std::endl;
      std::cout << "[     case ]: " << pretty(*_input) << std::endl;
      std::cout << "[       is ]: " << pretty(is) << std::endl;
      std::cout << "[ expected ]: " << pretty(expected) << std::endl;
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
  BUILDER_METHOD(ClauseStack, context)
  BUILDER_METHOD(Lib::Stack<ClausePattern>, expected)
  BUILDER_METHOD(bool, premiseRedundant)
  BUILDER_METHOD(SimplifyingGeneratingInference*, rule)
  BUILDER_METHOD(Lib::Stack<Indexing::Index*>, indices)
  BUILDER_METHOD(std::function<void(SaturationAlgorithm&)>, setup)
  BUILDER_METHOD(OptionMap, options)
  BUILDER_METHOD(Lib::Stack<Condition>, preConditions)
  BUILDER_METHOD(Lib::Stack<Condition>, postConditions)

  template<class Rule>
  void run(GenerationTester<Rule>& simpl) {

    // set up saturation algorithm
    auto container = PlainClauseContainer();

    // init problem
    Problem p;
    auto ul = UnitList::empty();
    UnitList::pushFromIterator(ClauseStack::Iterator(_context), ul);
    p.addUnits(ul);
    Lib::env.setMainProblem(&p);

    Options o;
    for (const auto& kv : _options) {
      o.set(kv.first, kv.second);
      Lib::env.options->set(kv.first, kv.second);
    }
    MockedSaturationAlgorithm alg(p, o);
    _setup(alg);
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

    // check that the preconditions hold
    std::string s1, s2;
    for (auto c : _preConditions) {
      if (!c(s1, s2)) {
        s2.append(" (precondition)");
        testFail(s1, s2);
      }
    }

    // run rule
    _input->setStore(Clause::ACTIVE);
    container.add(_input);
    auto res = rule.generateSimplify(_input);

    // run checks
    auto& sExp = this->_expected;
    auto  sRes = Lib::Stack<Kernel::Clause*>::fromIterator(res.clauses);

    if (!TestUtils::permEq(sExp, sRes, [&](auto exp, auto res) { return exp.matches(simpl, res); })) {
      testFail(sRes, sExp);
    }

    if (_premiseRedundant != res.premiseRedundant) {
      auto wrapStr = [](bool b) -> std::string { return b ? "premise is redundant" : "premise is not redundant"; };
      testFail( wrapStr(res.premiseRedundant), wrapStr(_premiseRedundant));
    }

    // check that the postconditions hold
    for (auto c : _postConditions) {
      if (!c(s1, s2)) {
        s2.append(" (postcondition)");
        testFail(s1, s2);
      }
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

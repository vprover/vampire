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
  [] (vstring& s1, vstring& s2) {                          \
    bool res = (VAL1 == VAL2);                             \
    if (!res) {                                            \
      s1 = Int::toString(VAL1);                            \
      s1.append(" != ");                                   \
      s1.append(Int::toString(VAL2));                      \
      s2 = vstring(#VAL1);                                 \
      s2.append(" == ");                                   \
      s2.append(#VAL2);                                    \
    }                                                      \
    return res;                                            \
  }

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
class AsymmetricTest;
class SymmetricTest;

template<class Rule>
class GenerationTester
{
  Rule _rule;

public:

  GenerationTester(Rule rule) 
    : _rule(std::move(rule)) 
  {  }

  virtual bool eq(Kernel::Clause* lhs, Kernel::Clause* rhs)
  { return TestUtils::eqModACRect(lhs, rhs); }

  friend class AsymmetricTest;
  friend class SymmetricTest;
};

class AsymmetricTest
{
  using Clause = Kernel::Clause;
  using OptionMap = Stack<pair<vstring,vstring>>;
  using Condition = std::function<bool(vstring&, vstring&)>;
  Option<SimplifyingGeneratingInference*> _rule;
  Clause* _input;
  Stack<ClausePattern> _expected;
  Stack<Clause*> _context;
  bool _premiseRedundant;
  Stack<std::function<Indexing::Index*()>> _indices;
  OptionMap _options;
  Stack<Condition> _preConditions;
  Stack<Condition> _postConditions;

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

  AsymmetricTest() : _rule(), _input(NULL), _expected(), _premiseRedundant(false), _options() {}

#define BUILDER_METHOD(type, field)                                                                           \
  AsymmetricTest field(type field)                                                                            \
  {                                                                                                           \
    this->_##field = decltype(_##field)(std::move(field));                                                    \
    return *this;                                                                                             \
  }                                                                                                           \

  BUILDER_METHOD(Clause*, input)
  BUILDER_METHOD(Stack<Clause*>, context)
  BUILDER_METHOD(Stack<ClausePattern>, expected)
  BUILDER_METHOD(bool, premiseRedundant)
  BUILDER_METHOD(SimplifyingGeneratingInference*, rule)
  BUILDER_METHOD(Stack<std::function<Indexing::Index*()>>, indices)
  BUILDER_METHOD(OptionMap, options)
  BUILDER_METHOD(Stack<Condition>, preConditions)
  BUILDER_METHOD(Stack<Condition>, postConditions)

  template<class Rule>
  void run(GenerationTester<Rule>& simpl) {

    for (const auto& kv : _options) {
      env.options->set(kv.first, kv.second);
    }
    // set up clause container and indexing strucure
    auto container =  PlainClauseContainer();
    SimplifyingGeneratingInference& rule = *_rule.unwrapOrElse([&](){ return &simpl._rule; });
    Stack<Indexing::Index*> indices;
    for (auto i : _indices) {
      indices.push(i());
    }

    rule.setTestIndices(indices);
    for (auto i : indices) {
      i->attachContainer(&container);
    }

    // add the clauses to the index
    for (auto c : _context) {
      c->setStore(Clause::ACTIVE);
      container.add(c);
    }

    // check that the preconditions hold
    vstring s1, s2;
    for (auto c : _preConditions) {
      if (!c(s1, s2)) {
        s2.append(" (precondition)");
        testFail(s1, s2);
      }
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


    // check that the postconditions hold
    for (auto c : _postConditions) {
      if (!c(s1, s2)) {
        s2.append(" (postcondition)");
        testFail(s1, s2);
      }
    }


    // // tear down saturation algorithm
    // rule.InferenceEngine::detach();

  }
};

class SymmetricTest
{
  using Clause = Kernel::Clause;
  Option<SimplifyingGeneratingInference*> _rule;
  Stack<Clause*> _inputs;
  Stack<ClausePattern> _expected;
  bool _premiseRedundant;
  Stack<std::function<Indexing::Index*()>> _indices;

  template<class Is, class Expected>
  void testFail(Is const& is, Expected const& expected) {
      cout  << endl;
      cout << "[     case ]: " << pretty(_inputs) << endl;
      cout << "[       is ]: " << pretty(is) << endl;
      cout << "[ expected ]: " << pretty(expected) << endl;
      exit(-1);
  }

public:

  SymmetricTest() : _rule(), _expected(), _premiseRedundant(false) {}

#define _BUILDER_METHOD(type, field)                                                                          \
  SymmetricTest field(type field)                                                                             \
  {                                                                                                           \
    this->_##field = decltype(_##field)(std::move(field));                                                    \
    return *this;                                                                                             \
  }                                                                                                           \

  _BUILDER_METHOD(Stack<Clause*>, inputs)
  _BUILDER_METHOD(Stack<ClausePattern>, expected)
  _BUILDER_METHOD(bool, premiseRedundant)
  _BUILDER_METHOD(SimplifyingGeneratingInference*, rule)
  _BUILDER_METHOD(Stack<std::function<Indexing::Index*()>>, indices)


  template<class Rule>
  void run(GenerationTester<Rule>& simpl) {
    for (unsigned i = 0; i < _inputs.size(); i++) {
      // cout << "\tusing clause " << i << " as input... " << endl;
      Stack<Clause*> context;
      auto input = _inputs[i];
      for (unsigned j = 0; j < _inputs.size(); j++) 
        if (i != j) 
          context.push(_inputs[j]);
      run(simpl, input, context);
      // cout << "\t-> ok (clause " << i << " as input)" << endl;
    }
  }

  template<class Rule>
  void run(GenerationTester<Rule>& simpl, Clause* input, Stack<Clause*> context) {
    SimplifyingGeneratingInference* rule = _rule.unwrapOrElse([&](){ return &simpl._rule; });
    AsymmetricTest()
      .input(input)
      .context(context)
      .expected(_expected)
      .premiseRedundant(_premiseRedundant)
      .rule(rule)
      .indices(_indices)
      .run(simpl);
  }
};

#define __CREATE_GEN_TESTER CAT(__createGenTester_, UNIT_ID)

#define REGISTER_GEN_TESTER(t) const auto __CREATE_GEN_TESTER = []()  { return t; };

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

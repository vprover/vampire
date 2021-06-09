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
  Rule _rule;

public:
  GenerationTester() 
    : _rule() 
  {}

  virtual bool eq(Kernel::Clause const* lhs, Kernel::Clause const* rhs) const 
  { return TestUtils::eqModAC(lhs, rhs); }

  friend class TestCase;
};

class TestCase
{
  using Clause = Kernel::Clause;
  Clause* _input;
  Stack<ClausePattern> _expected;
  bool _premiseRedundant;

  template<class Is, class Expected>
  void testFail(Is const& is, Expected const& expected) {
      cout  << endl;
      cout << "[     case ]: " << pretty(*_input) << endl;
      cout << "[       is ]: " << pretty(is) << endl;
      cout << "[ expected ]: " << pretty(expected) << endl;
      exit(-1);
  }

public:

  TestCase() : _input(NULL), _expected(), _premiseRedundant(false) {}


  TestCase input(Kernel::Clause* input) 
  { 
    this->_input = input; 
    return *this;
  }

  TestCase expected(Stack<ClausePattern> expected)
  {
    this->_expected = expected;
    return *this;
  }

  TestCase premiseRedundant(bool premiseRedundant)
  {
    this->_premiseRedundant = premiseRedundant;
    return *this;
  }

  template<class Rule>
  void run(GenerationTester<Rule>& simpl) {

    // set up saturation algorithm
    Problem p;
    Options o;
    MockedSaturationAlgorithm alg(p, o);
    simpl._rule.attach(&alg);

    // run rule
    auto res = simpl._rule.generateSimplify(_input);

    // run checks
    auto& sExp = this->_expected;
    auto  sRes = Stack<Kernel::Clause*>::fromIterator(res.clauses);

    auto iExp = getArrayishObjectIterator<mut_ref_t>(sExp);
    auto iRes = getArrayishObjectIterator<mut_ref_t>(sRes);

    while (iRes.hasNext() && iExp.hasNext()) {
      auto& exp = iExp.next();
      auto& res = iRes.next();
      if (!exp.matches(simpl, res)) {
        testFail(sRes, sExp);
      }
    }

    if (iExp.hasNext() || iRes.hasNext()) {
      testFail(sRes, sExp);
    }

    if (_premiseRedundant != res.premiseRedundant) {
      auto wrapStr = [](bool b) { return b ? "premise is redundant" : "premis not redundant"; };
      testFail( wrapStr(res.premiseRedundant), wrapStr(_premiseRedundant));
    }

    // tear down saturation algorithm
    simpl._rule.detach();
  }
};

#define REGISTER_GEN_TESTER(t) using __GenerationTester = t;

#define TEST_GENERATION(name, ...)                                                                            \
        TEST_GENERATION_WITH_SUGAR(name, MY_SYNTAX_SUGAR, __VA_ARGS__) 

#define TEST_GENERATION_WITH_SUGAR(name, syntax_sugar, ...)                                                   \
  TEST_FUN(name) {                                                                                            \
    __GenerationTester tester;                                                                                \
    __ALLOW_UNUSED(syntax_sugar)                                                                              \
    auto test = __VA_ARGS__;                                                                                  \
    test.run(tester);                                                                                         \
  }                                                                                                           \

} // namespace Simplification

} // namespace Test

#endif // __TEST__GENERATION_TESTER_HPP__

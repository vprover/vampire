/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __TEST__SIMPLIFICATION_TESTER_HPP__
#define __TEST__SIMPLIFICATION_TESTER_HPP__

/**
 * This file provides macros and classes used to write nice tests for simplification rules.
 *
 * Check out UnitTests/tGaussianElimination.cpp, to see how it is to be used.
 */

#include "Test/ClausePattern.hpp"
#include "Test/GenerationTester.hpp"
#include "Test/TestUtils.hpp"
#include "Kernel/Clause.hpp"
#include "Lib/Coproduct.hpp"

namespace Test {

namespace Simplification {

struct SimplificationTester : public Generation::GenerationTester
{
  SimplificationTester(SaturationAlgorithm& salg)
    : Generation::GenerationTester(salg) {}

  bool eq(Kernel::Clause* lhs, Kernel::Clause* rhs) override 
  { return TestUtils::eqModAC(lhs, rhs); }
};

class Redundant { };

// TODO use builder pattern macros from GenerationTester here
class Success
{
  Kernel::Clause* _input = nullptr;
  Option<Coproduct<ClausePattern, Redundant>> _expected;

public:
  Success input(Kernel::Clause* x) 
  {
    _input = x;
    return *this;
  }

  Success expected(Redundant x)
  {
    _expected = some(Coproduct<ClausePattern, Redundant>(x)); 
    return *this;
  }

  Success expected(ClausePattern x)
  {
    _expected = some(Coproduct<ClausePattern, Redundant>(x)); 
    return *this;
  }

  template<typename Rule, typename Tester, bool withSaturation = false>
  void run() {
    Problem prb;
    Options opt;
    opt.resolveAwayAutoValues(prb);
    MockedSaturationAlgorithm alg(prb, opt);

    Clause* res;
    if constexpr (withSaturation) {
      Rule rule(alg);
      res = rule.simplify(_input);
    } else {
      Rule rule;
      res = rule.simplify(_input);
    }
    Tester tester(alg);

    return _expected->match(
        [&](ClausePattern& expected) {
          if (!res) {
            std::cout  << std::endl;
            std::cout << "[     case ]: " << pretty(*_input) << std::endl;
            std::cout << "[       is ]: NULL (indicates the clause is a tautology)" << std::endl;
            std::cout << "[ expected ]: " << pretty(expected) << std::endl;
            exit(-1);

          } else if (!expected.matches(tester, res)) {
            std::cout  << std::endl;
            std::cout << "[     case ]: " << pretty(*_input) << std::endl;
            std::cout << "[       is ]: " << pretty(*res) << std::endl;
            std::cout << "[ expected ]: " << pretty(expected) << std::endl;
            exit(-1);
          }
        },        
        [&](Redundant&) {
          if (res) {
            std::cout  << std::endl;
            std::cout << "[     case ]: " << pretty(*_input) << std::endl;
            std::cout << "[       is ]: " << pretty(*res) << std::endl;
            std::cout << "[ expected ]: redundant" << std::endl;
            exit(-1);
          }
        });
  }
};

class NotApplicable
{
  Kernel::Clause* _input;
public:
  NotApplicable input(Kernel::Clause* x) 
  {
    _input = x;
    return *this;
  }

  template<typename Rule, typename Tester, bool withSaturation = false>
  void run() {
    Problem prb;
    Options opt;
    opt.resolveAwayAutoValues(prb);
    MockedSaturationAlgorithm alg(prb, opt);

    Clause* res;
    if constexpr (withSaturation) {
      Rule rule(alg);
      res = rule.simplify(_input);
    } else {
      Rule rule;
      res = rule.simplify(_input);
    }
    if (res != _input) {
      std::cout  << std::endl;
      std::cout << "[     case ]: " << pretty(*_input) << std::endl;
      std::cout << "[       is ]: " << pretty(*res) << std::endl;
      std::cout << "[ expected ]: < nop >" << std::endl;
      exit(-1);
    }
  }
};

class NotApplicableMany
{
  Kernel::Clause* _input;
public:
  NotApplicableMany input(Kernel::Clause* x)
  {
    _input = x;
    return *this;
  }

  template<typename Rule, typename Tester>
  void run() {
    Rule simpl;
    auto resOp = simpl.simplifyMany(_input);
    if (resOp.isSome()) {
      auto res = Stack<Kernel::Clause*>::fromIterator(std::move(*resOp));
      std::cout  << std::endl;
      std::cout << "[     case ]: " << pretty(*_input) << std::endl;
      std::cout << "[       is ]: " << pretty(res) << std::endl;
      std::cout << "[ expected ]: < nop >" << std::endl;
      exit(-1);
    }
  }
};

class SuccessMany
{
  Kernel::Clause* _input = nullptr;
  Option<StackMatcher> _expected;
public:
  SuccessMany input(Kernel::Clause* x)
  {
    _input = x;
    return *this;
  }

  SuccessMany expected(StackMatcher x)
  {
    _expected = some(x);
    return *this;
  }

  template<typename Rule, typename Tester>
  void run() {
    Problem prb;
    Options opt;
    opt.resolveAwayAutoValues(prb);
    MockedSaturationAlgorithm alg(prb, opt);

    Rule rule;
    auto resOp = rule.simplifyMany(_input);
    auto exp = _expected.unwrap();
    if (resOp.isNone()) {
      std::cout  << std::endl;
      std::cout << "[     case ]: " << pretty(*_input) << std::endl;
      std::cout << "[       is ]: < nop >" << std::endl;
      std::cout << "[ expected ]: " << pretty(exp) << std::endl;
      exit(-1);
    } else {
      Tester tester(alg);
      auto res = Stack<Kernel::Clause*>::fromIterator(std::move(*resOp));
      if (!exp.matches(res, tester)) {
        std::cout  << std::endl;
        std::cout << "[     case ]: " << pretty(*_input) << std::endl;
        std::cout << "[       is ]: " << pretty(res) << std::endl;
        std::cout << "[ expected ]: " << pretty(exp) << std::endl;
        exit(-1);
      }
    }
  }
};

#define TEST_SIMPLIFY(name, ...)                                                                              \
        TEST_SIMPLIFY_WITH_SUGAR(name, MY_SIMPL_RULE, MY_SIMPL_TESTER, MY_SYNTAX_SUGAR, __VA_ARGS__)

#define TEST_SIMPLIFY_WITH_SUGAR(name, rule, tester, syntax_sugar, test, ...)                                 \
  TEST_FUN(name) {                                                                                            \
    __ALLOW_UNUSED(syntax_sugar)                                                                              \
    test.run<rule, tester>(__VA_ARGS__);                                                                      \
  }                                                                                                           \

#define TEST_SIMPLIFY_WITH_SATURATION(name, test, ...)                                                        \
  TEST_FUN(name) {                                                                                            \
    __ALLOW_UNUSED(MY_SYNTAX_SUGAR)                                                                           \
    test.run<MY_SIMPL_RULE, MY_SIMPL_TESTER, /* withSaturation=*/ true>(__VA_ARGS__);                         \
  }                                                                                                           \

#define TEST_SIMPLIFY_MANY(name, ...)                                                                         \
        TEST_SIMPLIFY_MANY_WITH_SUGAR(name, MY_SIMPL_RULE, MY_SIMPL_TESTER, MY_SYNTAX_SUGAR, __VA_ARGS__)

#define TEST_SIMPLIFY_MANY_WITH_SUGAR(name, rule, tester, syntax_sugar, test, ...)                            \
  TEST_FUN(name) {                                                                                            \
    __ALLOW_UNUSED(syntax_sugar)                                                                              \
    test.run<rule, tester>(__VA_ARGS__);                                                                      \
  }                                                                                                           \

} // namespace Simplification

} // namespace Test

#endif // __TEST__SIMPLIFICATION_TESTER_HPP__

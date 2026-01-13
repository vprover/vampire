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

class SimplificationTester
{
public:
  virtual Kernel::Clause* simplify(Kernel::Clause*) = 0;

  virtual bool eq(Kernel::Clause* lhs, Kernel::Clause* rhs) const 
  { return TestUtils::eqModAC(lhs, rhs); }
};

template<typename T>
class RuleSimplificationTester
  : public SimplificationTester
{
  T _rule;
public:
  Kernel::Clause* simplify(Kernel::Clause* cl) override
  { return _rule.simplify(cl); }
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

  void run(SimplificationTester& simpl) {
    auto res = simpl.simplify(_input);

    return _expected->match(
        [&](ClausePattern& expected) {
          if (!res) {
            std::cout  << std::endl;
            std::cout << "[     case ]: " << pretty(*_input) << std::endl;
            std::cout << "[       is ]: NULL (indicates the clause is a tautology)" << std::endl;
            std::cout << "[ expected ]: " << pretty(expected) << std::endl;
            exit(-1);

          } else if (!expected.matches(simpl, res)) {
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

  void run(SimplificationTester& simpl) {
    auto res = simpl.simplify(_input);
    if (res != _input) {
      std::cout  << std::endl;
      std::cout << "[     case ]: " << pretty(*_input) << std::endl;
      std::cout << "[       is ]: " << pretty(*res) << std::endl;
      std::cout << "[ expected ]: < nop >" << std::endl;
      exit(-1);
    }
  }
};

template<class Rule>
class SimplificationManyTester
  : public Generation::GenerationTester<Rule>
{
public:
  SimplificationManyTester(Rule rule)
    : Generation::GenerationTester<Rule>(rule)
  {  }
  virtual Option<ClauseIterator> simplifyMany(Kernel::Clause*) = 0;
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

  template<class Rule>
  void run(SimplificationManyTester<Rule>& simpl) {
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

  template<class Rule>
  void run(SimplificationManyTester<Rule>& simpl) {
    auto resOp = simpl.simplifyMany(_input);
    auto exp = _expected.unwrap();
    if (resOp.isNone()) {
      std::cout  << std::endl;
      std::cout << "[     case ]: " << pretty(*_input) << std::endl;
      std::cout << "[       is ]: < nop >" << std::endl;
      std::cout << "[ expected ]: " << pretty(exp) << std::endl;
      exit(-1);
    } else {
      auto res = Stack<Kernel::Clause*>::fromIterator(std::move(*resOp));
      if (!exp.matches(res, simpl)) {
        std::cout  << std::endl;
        std::cout << "[     case ]: " << pretty(*_input) << std::endl;
        std::cout << "[       is ]: " << pretty(res) << std::endl;
        std::cout << "[ expected ]: " << pretty(exp) << std::endl;
        exit(-1);
      }
    }
  }
};


#define REGISTER_SIMPL_TESTER(t) using SimplTester = t;

#define TEST_SIMPLIFY(name, ...)                                                                              \
        TEST_SIMPLIFY_WITH_SUGAR(name, MY_SYNTAX_SUGAR, __VA_ARGS__) 

#define TEST_SIMPLIFY_WITH_SUGAR(name, syntax_sugar, ...)                                                     \
  TEST_FUN(name) {                                                                                            \
    SimplTester simpl;                                                                                        \
    __ALLOW_UNUSED(syntax_sugar)                                                                              \
    __VA_ARGS__.run(simpl);                                                                                   \
  }                                                                                                           \


#define REGISTER_SIMPL_MANY_TESTER(t) using SimplManyTester = t;

#define TEST_SIMPLIFY_MANY(name, ...)                                                                         \
        TEST_SIMPLIFY_MANY_WITH_SUGAR(name, MY_SYNTAX_SUGAR, __VA_ARGS__)

#define TEST_SIMPLIFY_MANY_WITH_SUGAR(name, syntax_sugar, ...)                                                \
  TEST_FUN(name) {                                                                                            \
    SimplManyTester simpl;                                                                                    \
    __ALLOW_UNUSED(syntax_sugar)                                                                              \
    __VA_ARGS__.run(simpl);                                                                                   \
  }                                                                                                           \

} // namespace Simplification

} // namespace Test

#endif // __TEST__SIMPLIFICATION_TESTER_HPP__

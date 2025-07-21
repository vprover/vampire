/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __TEST__SIMPLIFICATION_MANY_TESTER_HPP__
#define __TEST__SIMPLIFICATION_MANY_TESTER_HPP__

/**
 * This file provides macros and classes used to write nice tests for simplification rules.
 *
 * Check out UnitTests/tGaussianElimination.cpp, to see how it is to be used.
 */

#include "Forwards.hpp"
#include "Test/TestUtils.hpp"
#include "Test/ClausePattern.hpp"
#include "Kernel/Clause.hpp"
#include "Lib/Coproduct.hpp"
#include "Test/UnitTesting.hpp"
#include "Test/GenerationTester.hpp"

namespace Test {

namespace SimplificationMany {


class SimplificationManyTester : public ClauseMatchConfig
{
public:
  virtual Option<Kernel::ClauseIterator> simplifyMany(Kernel::Clause*) = 0;
};

class Redundant { };

// TODO use builder pattern macros from GenerationTester here
class Success
{
  Kernel::Clause* _input;
  Option<Coproduct<StackMatcher, Redundant>> _expected;

public:
  Success() : _input(nullptr) {}

  Success input(Kernel::Clause* x) 
  {
    _input = x;
    return *this;
  }

  Success expected(Redundant x)
  {
    _expected = some(Coproduct<StackMatcher, Redundant>(x)); 
    return *this;
  }

  Success expected(StackMatcher x)
  {
    _expected = some(Coproduct<StackMatcher, Redundant>(x)); 
    return *this;
  }

  // template<class... Patterns>
  // Success expected(ClausePattern x, Patterns... patterns)
  // { return expected(StackMatcherStack<ClausePattern>{ x, patterns... }); }

  void run(SimplificationManyTester& simpl) {
    _input = simpl.normalize(_input);
    auto res = iterTraits(simpl.simplifyMany(_input).unwrap())
      .map([&](auto c) { return simpl.normalize(c); })
      .collectStack();

    return _expected->match(
        [&](StackMatcher& _expected) {
          auto expected = _expected.mapClauses([&](auto c) { return simpl.normalize(c); });
          if (res.size() == 1 && res[0] == nullptr) {
            std::cout  << std::endl;
            std::cout << "[     case ]: " << pretty(*_input) << std::endl;
            std::cout << "[       is ]: NULL (indicates the clause is a tautology)" << std::endl;
            std::cout << "[ expected ]: " << pretty(expected) << std::endl;
            exit(-1);

          } else if (!expected.matches(res, simpl)) {
            std::cout  << std::endl;
            std::cout << "[     case ]: " << pretty(*_input) << std::endl;
            std::cout << "[       is ]: " << pretty(res) << std::endl;
            std::cout << "[ expected ]: " << pretty(expected) << std::endl;
            exit(-1);
          }
        },        
        [&](Redundant&) {
          if (res.size() != 1 || res[0] != nullptr) {
            std::cout  << std::endl;
            std::cout << "[     case ]: " << pretty(*_input) << std::endl;
            std::cout << "[       is ]: " << pretty(res) << std::endl;
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
  NotApplicable() {}

  NotApplicable input(Kernel::Clause* x) 
  {
    _input = x;
    return *this;
  }


  void run(SimplificationManyTester& simpl) {
    auto res = simpl.simplifyMany(_input);
    if (res.isSome()) {
      std::cout  << std::endl;
      std::cout << "[     case ]: " << pretty(*_input) << std::endl;
      std::cout << "[       is ]: " << pretty(iterTraits(*res).collectStack()) << std::endl;
      std::cout << "[ expected ]: < nop >" << std::endl;
      exit(-1);
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

} // namespace Simplification

} // namespace Test

#endif // __TEST__SIMPLIFICATION_MANY_TESTER_HPP__

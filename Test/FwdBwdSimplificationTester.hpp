/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __TEST__FWD_BWD_SIMPLIFICATION_TESTER_HPP__
#define __TEST__FWD_BWD_SIMPLIFICATION_TESTER_HPP__

/**
 * This file provides macros and classes used to write nice tests for generating inference rules.
 *
 * \see UnitTests/tEqualityResolution.cpp, for usage a example
 *
 * Don't rely on any part of the interface, but the things contained in the examples,
 * because it's rather unstable.
 */
#include "TestUtils.hpp"
#include "ClausePattern.hpp"
#include "MockedSaturationAlgorithm.hpp"
#include "BuilderPattern.hpp"
#include "UnitTesting.hpp"

#include "Kernel/Clause.hpp"

namespace Test {

namespace FwdBwdSimplification {
class TestCase;

template<class Rule>
class FwdBwdSimplificationTester
{
  Rule _rule;

public:
  FwdBwdSimplificationTester(Rule rule) 
    : _rule(std::move(rule)) 
  {  }

  virtual bool eq(Kernel::Clause* lhs, Kernel::Clause* rhs) const 
  { return TestUtils::eqModAC(lhs, rhs); }

  friend class TestCase;
};

class TestCase
{
  using Clause = Kernel::Clause;

  void testFail(std::string const& test, Lib::Exception& e) 
  {
      std::cout  << std::endl;
      std::cout << "[         test ]: " <<                  test  << std::endl;
      std::cout << "[   toSimplify ]: " << pretty(  toSimplify()) << std::endl;
      std::cout << "[ simplifyWith ]: " << pretty(simplifyWith()) << std::endl;
      std::cout << "[    exception ]: " << std::endl;
      e.cry(std::cout);
      exit(-1);
  }

  template<class Is, class Expected>
  void testFail(std::string const& test, Is const& is, Expected const& expected) 
  {
      std::cout  << std::endl;
      std::cout << "[         test ]: " <<                  test  << std::endl;
      std::cout << "[   toSimplify ]: " << pretty(  toSimplify()) << std::endl;
      std::cout << "[ simplifyWith ]: " << pretty(simplifyWith()) << std::endl;
      std::cout << "[           is ]: " << pretty(            is) << std::endl;
      std::cout << "[     expected ]: " << pretty(      expected) << std::endl;
      exit(-1);
  }

public:
  BUILDER_METHOD(TestCase, Stack<Clause*>, simplifyWith)
  BUILDER_METHOD(TestCase, Stack<Clause*>, toSimplify  )
  BUILDER_METHOD(TestCase, Stack<ClausePattern>, expected)
  BUILDER_METHOD(TestCase, Stack<ClausePattern>, justifications)
  BUILDER_METHOD(TestCase, ForwardSimplificationEngine* , fwd)
  BUILDER_METHOD(TestCase, BackwardSimplificationEngine*, bwd)
  BUILDER_METHOD(TestCase, OptionMap, options)

  void runFwd() 
  {
    Problem p;
    resetAndFillEnvOptions(options(), p);
    MockedSaturationAlgorithm alg(p, *env.options);
    // set up clause container and indexing structure
    auto container = alg.getSimplifyingClauseContainer();

    ForwardSimplificationEngine& fwd = *this->fwd().unwrap();
    fwd.attach(&alg);

    // add the clauses to the index
    auto simplifyWith = this->simplifyWith().unwrap();
    for (auto c : simplifyWith) {
      container->add(c);
    }

    // simplify all the clauses in toSimplify
    ClauseStack results;
    ClauseStack justifications;
    auto toSimpl = toSimplify().unwrap();
    for (auto toSimpl : toSimpl) {
      Clause* replacement = nullptr;
      ClauseIterator premises;
      bool succ;
      try {
        succ = fwd.perform(toSimpl, replacement, premises);
      } catch (Lib::Exception& e) { 
        testFail("fwd", e); 
      }

      if (succ) {
        if (replacement) {
          results.push(replacement);
        }
        justifications.loadFromIterator(std::move(premises));
      }
    }
    justifications.sort();
    justifications.dedup();
    fwd.detach();
    Ordering::unsetGlobalOrdering();

    // run checks
    auto expected = this->expected().unwrap();
    auto expJust = this->justifications().unwrapOrElse([&]()
        { return iterTraits(this->simplifyWith().unwrap().iterFifo())
                    .map([](Clause* cl) -> ClausePattern { return cl; } )
                    .template collect<Stack>(); });

    if (!TestUtils::permEq(expected, results, [&](auto exp, auto res) { return exp.matches(*this, res); })) {
      testFail("fwd", results, expected);
    }

    if (!TestUtils::permEq(expJust, justifications, [&](auto exp, auto res) { return exp.matches(*this, res); })) {
      testFail("fwd (justifications)", justifications, expJust);
    }
  }

  void runBwd() 
  {
    Problem p;
    resetAndFillEnvOptions(options(), p);
    MockedSaturationAlgorithm alg(p, *env.options);
    // set up clause container and indexing structure
    auto container = alg.getSimplifyingClauseContainer();

    BackwardSimplificationEngine& bwd = *this->bwd().unwrap();
    bwd.attach(&alg);

    // add the clauses to the index
    auto toSimpl = toSimplify().unwrap();
    for (auto c : toSimpl) {
      container->add(c);
    }

    // simplify using every clause in simplifyWith.unwrap()
    ClauseStack results; //= toSimplify().unwrap();
    auto simplifyWith = this->simplifyWith().unwrap();
    for (auto cl : simplifyWith) {
      Inferences::BwSimplificationRecordIterator simpls;
      try {
        bwd.perform(cl, simpls);
      } catch (Lib::Exception& e) { 
        testFail("bwd", e); 
      }
      for (auto simpl : iterTraits(std::move(simpls))) {
        if (simpl.replacement) {
          results.push(simpl.replacement);
        }
      }
    }
    bwd.detach();
    Ordering::unsetGlobalOrdering();

    // run checks
    auto expected = this->expected().unwrap();

    if (!TestUtils::permEq(expected, results, [&](auto exp, auto res) { return exp.matches(*this, res); })) {
      testFail("bwd", results, expected);
    }

  }


  void run() 
  {
    runFwd();
    if (fwd().isSome()) {
      delete fwd().unwrap();
    }

    runBwd();
    if (bwd().isSome()) {
      delete bwd().unwrap();
    }
  }

  template<class A>
  bool eq(A* lhs, A* rhs)  const
  { return TestUtils::eqModAC(lhs, rhs); }

};

#define TEST_SIMPLIFICATION(name, ...)                                                    \
        TEST_SIMPLIFICATION_WITH_SUGAR(name, MY_SYNTAX_SUGAR, __VA_ARGS__) 

#define TEST_SIMPLIFICATION_WITH_SUGAR(name, syntax_sugar, ...)                           \
  TEST_FUN(name) {                                                                        \
    __ALLOW_UNUSED(syntax_sugar)                                                          \
    auto test = __VA_ARGS__;                                                              \
    test.run();                                                                           \
  }                                                                                       \

} // namespace Simplification

} // namespace Test

#endif // __TEST__FWD_BWD_SIMPLIFICATION_TESTER_HPP__

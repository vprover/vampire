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
#include "Test/BuilderPattern.hpp"

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

  virtual bool eq(Kernel::Clause const* lhs, Kernel::Clause const* rhs) const 
  { return TestUtils::eqModAC(lhs, rhs); }

  friend class TestCase;
};

class TestCase
{
  using Clause = Kernel::Clause;

  template<class Is, class Expected>
  void testFail(vstring const& test, Is const& is, Expected const& expected) 
  {
      cout  << endl;
      cout << "[         test ]: " <<                  test  << endl;
      cout << "[   toSimplify ]: " << pretty(  toSimplify()) << endl;
      cout << "[ simplifyWith ]: " << pretty(simplifyWith()) << endl;
      cout << "[           is ]: " << pretty(            is) << endl;
      cout << "[     expected ]: " << pretty(      expected) << endl;
      exit(-1);
  }

public:

  BUILDER_METHOD(TestCase, Stack<Clause*>, simplifyWith)
  BUILDER_METHOD(TestCase, Stack<Clause*>, toSimplify  )
  BUILDER_METHOD(TestCase, Stack<ClausePattern>, expected)
  BUILDER_METHOD(TestCase, Stack<ClausePattern>, justifications)
  BUILDER_METHOD(TestCase, ForwardSimplificationEngine* , fwd)
  BUILDER_METHOD(TestCase, BackwardSimplificationEngine*, bwd)
  BUILDER_METHOD(TestCase, Stack<Indexing::Index*>, fwdIdx)
  BUILDER_METHOD(TestCase, Stack<Indexing::Index*>, bwdIdx)

  void runFwd() 
  {
    // set up clause container and indexing strucure
    auto container =  PlainClauseContainer();

    ForwardSimplificationEngine& fwd = *this->fwd().unwrap();

    auto indices = this->fwdIdx().unwrapOr(Stack<Indexing::Index*>());
    fwd.setTestIndices(indices);
    for (auto i : indices) {
      i->attachContainer(&container);
    }

    // add the clauses to the index
    for (auto c : simplifyWith().unwrap()) {
      container.add(c);
    }

    // simplify all the clauses in toSimplify
    Stack<Clause*> results;
    Stack<Clause*> justifications;
    for (auto toSimpl : toSimplify().unwrap()) {
      Clause* replacement = nullptr;
      ClauseIterator premises;
      auto succ = fwd.perform(toSimpl, replacement, premises);
      if (succ && replacement) {
        results.push(replacement);
      }
      results.loadFromIterator(premises);
    }

    // run checks
    auto expected = this->expected().unwrap();
    auto expJust = this->justifications().unwrap();

    if (!TestUtils::permEq(expected, results, [&](auto exp, auto res) { return exp.matches(*this, res); })) {
      testFail("fwd", results, expected);
    }

    if (!TestUtils::permEq(expJust, justifications, [&](auto exp, auto res) { return exp.matches(*this, res); })) {
      testFail("fwd (justifications)", results, expected);
    }
  }

  void runBwd() 
  {
    // set up clause container and indexing strucure
    auto container =  PlainClauseContainer();

    BackwardSimplificationEngine& bwd = *this->bwd().unwrap();

    auto indices = this->bwdIdx().unwrapOr(Stack<Indexing::Index*>());
    bwd.setTestIndices(indices);
    for (auto i : indices) {
      i->attachContainer(&container);
    }

    // add the clauses to the index
    for (auto c : toSimplify().unwrap()) {
      container.add(c);
    }

    // simplify using every clause in simplifyWith.unwrap()
    Stack<Clause*> results = toSimplify().unwrap();
    for (auto cl : simplifyWith().unwrap()) {
      Inferences::BwSimplificationRecordIterator simpls;
      bwd.perform(cl, simpls);
      for (auto simpl : iterTraits(simpls)) {
        results = iterTraits(results.iterFifo())
          .filterMap([&](auto r) 
            { return r != simpl.toRemove ? Option<Clause*>(r)
                     : simpl.replacement ? Option<Clause*>(simpl.replacement) : Option<Clause*>(); })
          .template collect<Stack>();
      }
    }

    // run checks
    auto expected = this->expected().unwrap();

    if (!TestUtils::permEq(expected, results, [&](auto exp, auto res) { return exp.matches(*this, res); })) {
      testFail("bwd", results, expected);
    }

  }


  void run() 
  {
    runFwd();
    runBwd();
  }

  template<class A>
  bool eq(A* lhs, A* rhs)  const
  { return TestUtils::eqModAC(lhs, rhs); }

};

#define __CREATE_GEN_TESTER CAT(__createGenTester_, UNIT_ID)

#define REGISTER_GEN_TESTER(t) auto __CREATE_GEN_TESTER() { return t; }

#define TEST_SIMPLIFICATION(name, ...)                                                                        \
        TEST_SIMPLIFICATION_WITH_SUGAR(name, MY_SYNTAX_SUGAR, __VA_ARGS__) 

#define TEST_SIMPLIFICATION_WITH_SUGAR(name, syntax_sugar, ...)                                               \
  TEST_FUN(name) {                                                                                            \
    __ALLOW_UNUSED(syntax_sugar)                                                                              \
    auto test = __VA_ARGS__;                                                                                  \
    test.run();                                                                                               \
  }                                                                                                           \

} // namespace Simplification

} // namespace Test

#endif // __TEST__FWD_BWD_SIMPLIFICATION_TESTER_HPP__

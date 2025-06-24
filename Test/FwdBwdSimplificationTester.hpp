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

#include "Inferences/InferenceEngine.hpp"
#include "Test/TestUtils.hpp"
#include "Kernel/Clause.hpp"
#include "Test/ClausePattern.hpp"
#include "Test/BuilderPattern.hpp"

namespace Test {

  /** removes consecutive duplicates. instead of the operator== the given predicate is used */
  template<class A, class Equal>
  void dedup(Stack<A>& self, Equal eq)
{ 
    if (self.size() == 0) return;
    unsigned offs = 0;
    for (unsigned i = 1;  i < self.size(); i++) {
      if (eq(self[offs], self[i])) {
        /* skip */
      } else {
        self[offs++ + 1] = std::move(self[i]);
      }
    }
    self.pop(self.size() - (offs + 1));
  }

  /** removes consecutive duplicates */
  template<class A>
  void dedup(Stack<A>& self)
  { dedup(self, [](auto const& l, auto const& r) { return l == r; }); }


namespace FwdBwdSimplification {

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
  using NormFun = std::function<Clause*(Clause*)>;

  BUILDER_METHOD(TestCase, Stack<Clause*>, simplifyWith)
  BUILDER_METHOD(TestCase, Stack<Clause*>, toSimplify  )
  BUILDER_METHOD(TestCase, Stack<ClausePattern>, expected)
  BUILDER_METHOD(TestCase, NormFun, normalize)
  BUILDER_METHOD(TestCase, Stack<ClausePattern>, justifications)
  BUILDER_METHOD(TestCase, Inferences::ForwardSimplificationEngine* , fwd)
  BUILDER_METHOD(TestCase, Inferences::BackwardSimplificationEngine*, bwd)
  BUILDER_METHOD(TestCase, Stack<Indexing::Index*>, fwdIdx)
  BUILDER_METHOD(TestCase, Stack<Indexing::Index*>, bwdIdx)


  TestCase expectNotApplicable() && 
  { return expected({}).justifications({}); }

  void runFwd() 
  {
    // set up clause container and indexing structure
    auto container =  PlainClauseContainer();

    auto& fwd = *this->fwd().unwrap();

    // run checks
    auto expected = this->expected().unwrap();
    auto expJust = this->justifications().unwrapOrElse([&]()
        { return iterTraits(this->simplifyWith().unwrap().iterFifo())
                    .map([](Clause* cl) -> ClausePattern { return cl; } )
                    .template collect<Stack>(); });

    // add the clauses to the index
    auto simplifyWith = this->simplifyWith().unwrap();
    auto toSimpl = toSimplify().unwrap();

    auto norm = [this](auto x) {
      if (this->normalize()) { return (*this->normalize())(x); }
      else                   { return x; }
    };

    for (Clause*& c : simplifyWith) { c = norm(c); }
    for (Clause*& c : toSimpl) { c = norm(c); }
    for (ClausePattern& c : concatIters(arrayIter(expected), arrayIter(expJust))) {
      c = c.mapClauses([&](auto c) { return norm(c); });
    }

    auto indices = this->fwdIdx().unwrapOr(Stack<Indexing::Index*>());
    fwd.setTestIndices(indices);
    for (auto i : indices) {
      i->attachContainer(&container);
    }

    for (auto c : simplifyWith) {
      container.add(c);
    }

    // simplify all the clauses in toSimplify
    Stack<Clause*> results;
    Stack<Clause*> justifications;
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
          results.push(norm(replacement));
        }
        justifications.loadFromIterator(premises);
      }
    }
    justifications.sort();
    justifications.dedup();
    // dedup(justifications);

    if (!TestUtils::permEq(expected, results, [&](auto exp, auto res) { return exp.matches(*this, res); })) {
      testFail("fwd", results, expected);
    }

    if (!TestUtils::permEq(expJust, justifications, [&](auto exp, auto res) { return exp.matches(*this, res); })) {
      testFail("fwd (justifications)", justifications, expJust);
    }
  }

  void runBwd() 
  {
    // set up clause container and indexing structure
    auto container =  PlainClauseContainer();

    auto& bwd = *this->bwd().unwrap();

    // run checks
    auto expected = this->expected().unwrap();
    auto expJust = this->justifications().unwrapOrElse([&]()
        { return iterTraits(this->simplifyWith().unwrap().iterFifo())
                    .map([](Clause* cl) -> ClausePattern { return cl; } )
                    .template collect<Stack>(); });

    // add the clauses to the index
    auto simplifyWith = this->simplifyWith().unwrap();
    auto toSimpl = toSimplify().unwrap();

    auto norm = [this](auto x) {
      if (this->normalize()) { return (*this->normalize())(x); }
      else                   { return x; }
    };

    for (Clause*& c : simplifyWith) { c = norm(c); }
    for (Clause*& c : toSimpl) { c = norm(c); }
    for (ClausePattern& c : concatIters(arrayIter(expected), arrayIter(expJust))) {
      c = c.mapClauses([&](auto c) { return norm(c); });
    }

    auto indices = this->bwdIdx().unwrapOr(Stack<Indexing::Index*>());
    bwd.setTestIndices(indices);
    for (auto i : indices) {
      i->attachContainer(&container);
    }

    // add the clauses to the index
    for (auto c : toSimpl) {
      container.add(c);
    }

    // simplify using every clause in simplifyWith
    Stack<Clause*> results;
    for (auto cl : simplifyWith) {
      Inferences::BwSimplificationRecordIterator simpls;
      try {
        bwd.perform(cl, simpls);
      } catch (Lib::Exception& e) { 
        testFail("bwd", e); 
      }
      for (auto simpl : iterTraits(simpls)) {
        results.push(norm(simpl.replacement));
      }
    }

    // run checks
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

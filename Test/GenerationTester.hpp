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
 * Don't rely on any part of the interface, but the things contained in the examples,
 * because it's rather unstable.
 */

#include "Forwards.hpp"
#include "Test/TestUtils.hpp"
#include "Kernel/Clause.hpp"
#include "Lib/Coproduct.hpp"
#include "Test/ClausePattern.hpp"
#include "Test/BuilderPattern.hpp"
#include "Kernel/Problem.hpp"
#include "UnitTesting.hpp"
#include "Lib/STL.hpp"
#include "Test/MockedSaturationAlgorithm.hpp"

namespace Test {

namespace Generation {
class GenerationTester;
}

class ContainsStackMatcher {
  Stack<ClausePattern> _patterns;

public:
  ContainsStackMatcher(Stack<ClausePattern> self) : _patterns(self) {}

  bool matches(Stack<Kernel::Clause*> sRes, Generation::GenerationTester& simpl) 
  { 
    return iterTraits(_patterns.iter())
      .all([&](auto& p) {
          return iterTraits(sRes.iter())
             .any([&](Kernel::Clause* cl) { return p.matches(simpl, cl); });
      });
  }

  template<class F>
  ContainsStackMatcher mapClauses(F fun) const {
    return ContainsStackMatcher(arrayIter(_patterns)
        .map([&](auto& c) { return c.mapClauses(fun); })
        .template collect<Stack>()); }

  friend std::ostream& operator<<(std::ostream& out, ContainsStackMatcher const& self)
  { return out << "contains: " << self._patterns; }
};


class StackMatcher;
std::ostream& operator<<(std::ostream& out, StackMatcher const& self);

class ExactlyStackMatcher {
  Stack<ClausePattern> _patterns;

public:
  ExactlyStackMatcher(Stack<ClausePattern> self) : _patterns(self) {}

  template<class F>
  ExactlyStackMatcher mapClauses(F fun) const {
    return ExactlyStackMatcher(arrayIter(_patterns)
        .map([&](auto& c) { return c.mapClauses(fun); })
        .template collect<Stack>()); }

  bool matches(Stack<Kernel::Clause*> sRes, Generation::GenerationTester& simpl) 
  { return TestUtils::permEq(_patterns, sRes, [&](auto exp, auto res) { return exp.matches(simpl, res); }); }

  friend std::ostream& operator<<(std::ostream& out, ExactlyStackMatcher const& self)
  { return out << "exactly: " << self._patterns; }
};

class WithoutDuplicatesMatcher {
  std::shared_ptr<StackMatcher> _inner;

public:
  WithoutDuplicatesMatcher(std::shared_ptr<StackMatcher> m) : _inner(std::move(m)) {}

  template<class F>
  WithoutDuplicatesMatcher mapClauses(F fun) const;

  bool matches(Stack<Kernel::Clause*> sRes, Generation::GenerationTester& simpl);

  friend std::ostream& operator<<(std::ostream& out, WithoutDuplicatesMatcher const& self)
  { return out << "without duplicates: " << *self._inner; }
};


using AnyStackMatcher = Coproduct< ContainsStackMatcher
                                 , WithoutDuplicatesMatcher
                                 , ExactlyStackMatcher>;

class StackMatcher
  : public AnyStackMatcher {
public:
  StackMatcher(std::initializer_list<ClausePattern> clauses) : StackMatcher(ExactlyStackMatcher(Stack<ClausePattern>(clauses))) {}
  template<class C> StackMatcher(C c) : AnyStackMatcher(std::move(c)) {}

  template<class F>
  StackMatcher mapClauses(F fun) const 
  { return apply([&](auto x) { return StackMatcher(x.mapClauses(fun)); }); }

  bool matches(Stack<Kernel::Clause*> sRes, Generation::GenerationTester& simpl) 
  { return apply([&](auto& self) { return self.matches(sRes, simpl); }); }

  friend std::ostream& operator<<(std::ostream& out, StackMatcher const& self)
  { return self.apply([&](auto& inner) -> decltype(auto) { return out << inner; }); }
};

template<class F>
WithoutDuplicatesMatcher WithoutDuplicatesMatcher::mapClauses(F fun) const 
{ return make_shared(_inner->mapClauses(fun)); }

inline bool WithoutDuplicatesMatcher::matches(Stack<Kernel::Clause*> sRes, Generation::GenerationTester& simpl)
{ 
  Stack<Stack<Literal*>> clauses;
  for (auto c : sRes) {
    clauses.push(c->iterLits().collect<Stack<Literal*>>().sorted());
  }
  clauses.sort();
  clauses.dedup();
  Stack<Kernel::Clause*> newRes;
  for (auto& c : clauses) {
    newRes.push(Clause::fromStack(c, Inference(FromInput(UnitInputType::ASSUMPTION))));
  }

  return _inner->matches(std::move(newRes), simpl); 
}

template<class... As>
StackMatcher exactly(As... as) 
{ return ExactlyStackMatcher(Stack<ClausePattern>({ as... })); }

inline StackMatcher withoutDuplicates(StackMatcher inner) 
{ return WithoutDuplicatesMatcher(std::shared_ptr<StackMatcher>(move_to_heap(std::move(inner)))); }


template<class... As>
StackMatcher contains(As... as) 
{ return ContainsStackMatcher(Stack<ClausePattern>({ as... })); }

inline StackMatcher none() 
{ return ExactlyStackMatcher(Stack<ClausePattern>()); }

namespace Generation {
class AsymmetricTest;
class SymmetricTest;

class GenerationTester
{
public:
  virtual ~GenerationTester() = default;
  virtual Clause* normalize(Kernel::Clause* c)
  { return c; }

  virtual bool eq(Kernel::Clause* lhs, Kernel::Clause* rhs)
  { return TestUtils::eqModACRect(lhs, rhs); }
};

class AsymmetricTest
{
  using Clause = Kernel::Clause;

  template<class Is, class Expected>
  void testFail(Is const& is, Expected const& expected) {
      std::cout  << std::endl;
      std::cout << "[  context ]: " << pretty(_context) << std::endl;
      std::cout << "[  options ]: " << pretty(_options) << std::endl;
      std::cout << "[     case ]: " << pretty(*_input) << std::endl;
      std::cout << "[       is ]: " << pretty(is) << std::endl;
      std::cout << "[ expected ]: " << pretty(expected) << std::endl;
      ASSERTION_VIOLATION
  }

public:

  AsymmetricTest() : _input(NULL), _expected(), _premiseRedundant(false), _selfApplications(true), _setup([](SaturationAlgorithm&){}), _options() {}

  __BUILDER_METHOD(AsymmetricTest, Clause*, input)
  __BUILDER_METHOD(AsymmetricTest, ClauseStack, context)
  BUILDER_METHOD(AsymmetricTest, StackMatcher, expected)
  __BUILDER_METHOD(AsymmetricTest, bool, premiseRedundant)
  __BUILDER_METHOD(AsymmetricTest, bool, selfApplications)
  __BUILDER_METHOD(AsymmetricTest, std::function<void(SaturationAlgorithm&)>, setup)
  __BUILDER_METHOD(AsymmetricTest, OptionMap, options)

  template<typename Rule, typename Tester, typename... Args>
  void run(Args... args) {

    Tester tester;

    for (auto& c : _context) {
      c = tester.normalize(c);
    }
    _input = tester.normalize(_input);

    // init problem
    Problem p;
    auto ul = UnitList::fromIterator(ClauseStack::Iterator(_context));
    p.addUnits(ul);
    env.setMainProblem(&p);

    resetAndFillEnvOptions(_options, p);
    MockedSaturationAlgorithm alg(p, *env.options);
    _setup(alg);
    Rule rule(alg, args...);

    auto container = alg.getActiveClauseContainer();

    // add the clauses to the index
    for (auto c : _context) {
      c->setStore(Clause::ACTIVE);
      container->add(c);
    }

    _input->setStore(Clause::ACTIVE);

    // run rule
    if (_selfApplications) {
      container->add(_input);
    }

    auto res = rule.generateSimplify(_input);

    // run checks
    auto sExp = this->_expected.unwrap();
    auto sRes = Stack<Kernel::Clause*>::fromIterator(std::move(res.clauses));

    if (!sExp.matches(sRes, tester)) {
      testFail(sRes, sExp);
    }

    if (_premiseRedundant != res.premiseRedundant) {
      auto wrapStr = [](bool b) -> std::string { return b ? "premise is redundant" : "premise is not redundant"; };
      testFail( wrapStr(res.premiseRedundant), wrapStr(_premiseRedundant));
    }

    // remove the clauses from the index
    for (auto c : _context) {
      // c->setStore(Clause::ACTIVE);
      container->remove(c);
    }

    Ordering::unsetGlobalOrdering();
  }
};

class SymmetricTest
{
  using Clause = Kernel::Clause;

  template<class Is, class Expected>
  void testFail(Is const& is, Expected const& expected) {
      std::cout  << std::endl;
      std::cout << "[     case ]: " << pretty(_inputs) << std::endl;
      std::cout << "[       is ]: " << pretty(is) << std::endl;
      std::cout << "[ expected ]: " << pretty(expected) << std::endl;
      exit(-1);
  }

public:

  SymmetricTest() : _expected(), _premiseRedundant(false), _selfApplications(true) {}

  __BUILDER_METHOD(SymmetricTest, Stack<Clause*>, inputs)
  BUILDER_METHOD(SymmetricTest, StackMatcher, expected)
  __BUILDER_METHOD(SymmetricTest, bool, premiseRedundant)
  __BUILDER_METHOD(SymmetricTest, bool, selfApplications)
  __BUILDER_METHOD(SymmetricTest, OptionMap, options)

  template<typename Rule, typename Tester, typename... Args>
  void run(Args... args) {
    for (unsigned i = 0; i < _inputs.size(); i++) {
      Stack<Clause*> context;
      auto input = _inputs[i];
      for (unsigned j = 0; j < _inputs.size(); j++) 
        if (i != j) 
          context.push(_inputs[j]);
      runInner<Rule, Tester, Args...>(input, context, args...);
    }
  }

  template<typename Rule, typename Tester, typename... Args>
  void runInner(Clause* input, Stack<Clause*> context, Args... args) {
    AsymmetricTest()
      .input(input)
      .context(context)
      .expected(_expected.unwrap())
      .premiseRedundant(_premiseRedundant)
      .selfApplications(_selfApplications)
      .options(_options)
      .run<Rule, Tester, Args...>(args...);
  }
};

#define __CREATE_GEN_TESTER CAT(__createGenTester_, UNIT_ID)

#define REGISTER_GEN_TESTER(t) const auto __CREATE_GEN_TESTER = []()  { return t; };

#define TEST_GENERATION(name, ...)                                                        \
  TEST_GENERATION_WITH_SUGAR(name, MY_GEN_RULE, MY_GEN_TESTER, MY_SYNTAX_SUGAR, __VA_ARGS__) 

#define TEST_GENERATION_WITH_SUGAR(name, rule, tester, syntax_sugar, test, ...)           \
  TEST_FUN(name) {                                                                        \
    __ALLOW_UNUSED(syntax_sugar)                                                          \
    test.run<rule,tester>(__VA_ARGS__);                                                   \
  }                                                                                       \

} // namespace Simplification

} // namespace Test

#endif // __TEST__GENERATION_TESTER_HPP__

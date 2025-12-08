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
#include "Kernel/Problem.hpp"
#include "Shell/Options.hpp"
#include "Lib/STL.hpp"
#include "Test/MockedSaturationAlgorithm.hpp"

namespace Test {

#define TEST_FN_ASS_EQ(VAL1, VAL2)                                                        \
  [] (std::string& s1, std::string& s2) {                                                 \
    bool res = (VAL1 == VAL2);                                                            \
    if (!res) {                                                                           \
      s1 = Int::toString(VAL1);                                                           \
      s1.append(" != ");                                                                  \
      s1.append(Int::toString(VAL2));                                                     \
      s2 = std::string(#VAL1);                                                            \
      s2.append(" == ");                                                                  \
      s2.append(#VAL2);                                                                   \
    }                                                                                     \
    return res;                                                                           \
  }

namespace Generation {
template<class R>
class GenerationTester;
}

class ContainsStackMatcher {
  Stack<ClausePattern> _patterns;

public:
  ContainsStackMatcher(Stack<ClausePattern> self) : _patterns(self) {}

  template<class Rule>
  bool matches(Stack<Kernel::Clause*> sRes, Generation::GenerationTester<Rule>& simpl) 
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

  template<class Rule>
  bool matches(Stack<Kernel::Clause*> sRes, Generation::GenerationTester<Rule>& simpl) 
  { return TestUtils::permEq(_patterns, sRes, [&](auto exp, auto res) { return exp.matches(simpl, res); }); }

  friend std::ostream& operator<<(std::ostream& out, ExactlyStackMatcher const& self)
  { return out << "exactly: " << self._patterns; }
};

class TodoStackMatcher {

public:
  TodoStackMatcher() {}

  template<class F>
  TodoStackMatcher mapClauses(F fun) const 
  { return TodoStackMatcher(); }

  template<class Rule>
  bool matches(Stack<Kernel::Clause*> sRes, Generation::GenerationTester<Rule>& simpl) 
  { return false; }

  friend std::ostream& operator<<(std::ostream& out, TodoStackMatcher const& self)
  { return out << "TODO"; }
};

class WithoutDuplicatesMatcher {
  std::shared_ptr<StackMatcher> _inner;

public:
  WithoutDuplicatesMatcher(std::shared_ptr<StackMatcher> m) : _inner(std::move(m)) {}

  template<class F>
  WithoutDuplicatesMatcher mapClauses(F fun) const;

  template<class Rule>
  bool matches(Stack<Kernel::Clause*> sRes, Generation::GenerationTester<Rule>& simpl);

  friend std::ostream& operator<<(std::ostream& out, WithoutDuplicatesMatcher const& self)
  { return out << "without duplicates: " << *self._inner; }
};


using AnyStackMatcher = Coproduct< ContainsStackMatcher
                                 , WithoutDuplicatesMatcher
                                 , ExactlyStackMatcher
                                 , TodoStackMatcher>;

class StackMatcher
  : public AnyStackMatcher {
public:
  StackMatcher(std::initializer_list<ClausePattern> clauses) : StackMatcher(ExactlyStackMatcher(Stack<ClausePattern>(clauses))) {}
  template<class C> StackMatcher(C c) : AnyStackMatcher(std::move(c)) {}

  template<class F>
  StackMatcher mapClauses(F fun) const 
  { return apply([&](auto x) { return StackMatcher(x.mapClauses(fun)); }); }

  template<class Rule>
  bool matches(Stack<Kernel::Clause*> sRes, Generation::GenerationTester<Rule>& simpl) 
  { return apply([&](auto& self) { return self.matches(sRes, simpl); }); }

  friend std::ostream& operator<<(std::ostream& out, StackMatcher const& self)
  { return self.apply([&](auto& inner) -> decltype(auto) { return out << inner; }); }
};

template<class F>
WithoutDuplicatesMatcher WithoutDuplicatesMatcher::mapClauses(F fun) const 
{ return make_shared(_inner->mapClauses(fun)); }


template<class Rule>
bool WithoutDuplicatesMatcher::matches(Stack<Kernel::Clause*> sRes, Generation::GenerationTester<Rule>& simpl)
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

inline StackMatcher EXPECTED_TODO()
{ return TodoStackMatcher(); }

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

template<class Rule>
class GenerationTester
{
protected:
  Rule _rule;

public:

  GenerationTester(Rule rule) 
    : _rule(std::move(rule)) 
  {  }

  virtual Clause* normalize(Kernel::Clause* c)
  { return c; }

  virtual bool eq(Kernel::Clause* lhs, Kernel::Clause* rhs)
  { return TestUtils::eqModACRect(lhs, rhs); }

  friend class AsymmetricTest;
  friend class SymmetricTest;
};

using TestIndices = Stack<std::function<Indexing::Index*(const SaturationAlgorithm&)>>;

class AsymmetricTest
{
  using Clause = Kernel::Clause;
  using OptionMap = Stack<std::pair<std::string,std::string>>;
  using Condition = std::function<bool(std::string&, std::string&)>;
  Option<SimplifyingGeneratingInference*> _rule;
  Clause* _input;
  Option<StackMatcher> _expected;
  Stack<Clause*> _context;
  bool _premiseRedundant;
  TestIndices _indices;
  std::function<void(SaturationAlgorithm&)> _setup = [](SaturationAlgorithm&){};
  bool _selfApplications;
  OptionMap _options;
  Stack<Condition> _preConditions;
  Stack<Condition> _postConditions;

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

  AsymmetricTest() : _rule(), _input(NULL), _expected(), _premiseRedundant(false), _selfApplications(true), _options() {}

  using Self = AsymmetricTest;
#define __BUILDER_METHOD(type, field)                                                     \
  Self field(type field)                                                                  \
  {                                                                                       \
    this->_##field = decltype(_##field)(std::move(field));                                \
    return *this;                                                                         \
  }                                                                                       \

  __BUILDER_METHOD(Clause*, input)
  __BUILDER_METHOD(ClauseStack, context)
  __BUILDER_METHOD(StackMatcher, expected)
  __BUILDER_METHOD(bool, premiseRedundant)
  __BUILDER_METHOD(bool, selfApplications)
  __BUILDER_METHOD(SimplifyingGeneratingInference*, rule)
  __BUILDER_METHOD(TestIndices, indices)
  __BUILDER_METHOD(std::function<void(SaturationAlgorithm&)>, setup)
  __BUILDER_METHOD(OptionMap, options)

#undef __BUILDER_METHOD

  template<class Rule>
  void run(GenerationTester<Rule>& simpl) {

    for (auto& c : _context) {
      c = simpl.normalize(c);
    }
    _input = simpl.normalize(_input);

    // set up saturation algorithm
    auto container = ActiveClauseContainer();

    // init problem
    Problem p;
    auto ul = UnitList::empty();
    UnitList::pushFromIterator(ClauseStack::Iterator(_context), ul);
    p.addUnits(ul);
    env.setMainProblem(&p);

    delete env.options;
    env.options = new Options;
    for (const auto& kv : _options) {
      env.options->set(kv.first, kv.second);
    }
    env.options->resolveAwayAutoValues0();
    env.options->resolveAwayAutoValues(p);
    MockedSaturationAlgorithm alg(p, *env.options);
    _setup(alg);
    SimplifyingGeneratingInference& rule = *_rule.unwrapOrElse([&](){ return &simpl._rule; });
    rule.InferenceEngine::attach(&alg);
    Stack<Indexing::Index*> indices;
    for (auto i : _indices) {
      indices.push(i(alg));
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

    // run rule
    if (_selfApplications) {
      _input->setStore(Clause::ACTIVE);
      container.add(_input);
    }

    auto res = rule.generateSimplify(_input);

    // run checks
    auto sExp = this->_expected.unwrap();
    auto sRes = Stack<Kernel::Clause*>::fromIterator(res.clauses);

    if (!sExp.matches(sRes, simpl)) {
      testFail(sRes, sExp);
    }

    if (_premiseRedundant != res.premiseRedundant) {
      auto wrapStr = [](bool b) -> std::string { return b ? "premise is redundant" : "premise is not redundant"; };
      testFail( wrapStr(res.premiseRedundant), wrapStr(_premiseRedundant));
    }

    // add the clauses to the index
    for (auto c : _context) {
      // c->setStore(Clause::ACTIVE);
      container.remove(c);
    }

    // // tear down saturation algorithm
    rule.InferenceEngine::detach();

    Ordering::unsetGlobalOrdering();
  }
};

class SymmetricTest
{
  using Clause = Kernel::Clause;
  Option<SimplifyingGeneratingInference*> _rule;
  Stack<Clause*> _inputs;
  Option<StackMatcher> _expected;
  bool _premiseRedundant;
  bool _selfApplications;
  TestIndices _indices;

  template<class Is, class Expected>
  void testFail(Is const& is, Expected const& expected) {
      std::cout  << std::endl;
      std::cout << "[     case ]: " << pretty(_inputs) << std::endl;
      std::cout << "[       is ]: " << pretty(is) << std::endl;
      std::cout << "[ expected ]: " << pretty(expected) << std::endl;
      exit(-1);
  }

public:

  SymmetricTest() : _rule(), _expected(), _premiseRedundant(false), _selfApplications(true) {}

#define __BUILDER_METHOD(type, field)                                                     \
  SymmetricTest field(type field)                                                         \
  {                                                                                       \
    this->_##field = decltype(_##field)(std::move(field));                                \
    return *this;                                                                         \
  }                                                                                       \

  __BUILDER_METHOD(Stack<Clause*>, inputs)
  __BUILDER_METHOD(StackMatcher, expected)
  __BUILDER_METHOD(bool, premiseRedundant)
  __BUILDER_METHOD(bool, selfApplications)
  __BUILDER_METHOD(SimplifyingGeneratingInference*, rule)
  __BUILDER_METHOD(TestIndices, indices)

#undef __BUILDER_METHOD


  template<class Rule>
  void run(GenerationTester<Rule>& simpl) {
    for (unsigned i = 0; i < _inputs.size(); i++) {
      Stack<Clause*> context;
      auto input = _inputs[i];
      for (unsigned j = 0; j < _inputs.size(); j++) 
        if (i != j) 
          context.push(_inputs[j]);
      run(simpl, input, context);
    }
  }

  template<class Rule>
  void run(GenerationTester<Rule>& simpl, Clause* input, Stack<Clause*> context) {
    SimplifyingGeneratingInference* rule = _rule.unwrapOrElse([&](){ return &simpl._rule; });
    AsymmetricTest()
      .input(input)
      .context(context)
      .expected(_expected.unwrap())
      .premiseRedundant(_premiseRedundant)
      .selfApplications(_selfApplications)
      .rule(rule)
      .indices(_indices)
      .run(simpl);
  }
};

#define __CREATE_GEN_TESTER CAT(__createGenTester_, UNIT_ID)

#define REGISTER_GEN_TESTER(t) const auto __CREATE_GEN_TESTER = []()  { return t; };

#define TEST_GENERATION(name, ...)                                                        \
        TEST_GENERATION_WITH_SUGAR(name, MY_SYNTAX_SUGAR, __VA_ARGS__) 

#define TEST_GENERATION_WITH_SUGAR(name, syntax_sugar, ...)                               \
  TEST_FUN(name) {                                                                        \
    auto tester = __CREATE_GEN_TESTER();                                                  \
    __ALLOW_UNUSED(syntax_sugar)                                                          \
    auto test = __VA_ARGS__;                                                              \
    test.run(tester);                                                                     \
  }                                                                                       \

} // namespace Simplification

} // namespace Test

#endif // __TEST__GENERATION_TESTER_HPP__

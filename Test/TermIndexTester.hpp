
  /*
   * File GenerationTester.hpp.
   *
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
#include "Kernel/Substitution.hpp"
#include "Indexing/TermIndex.hpp"

namespace Test {

template<class Field>
struct DefaultValue {
  using Type = typename Field::Type;
  static Option<Type> value() { return Option<Type>(); }
};

template<class C>
struct BuilderInitializer
{ using Type = C; };

template<class A>
struct BuilderInitializer<Stack<A>>
{ using Type = std::initializer_list<A>; };


#define BUILDER_METHOD(Self, ty, field)                                                                       \
private:                                                                                                      \
  Option<ty> _##field;                                                                                        \
                                                                                                              \
  Option<ty> field() const                                                                                    \
  {                                                                                                           \
    return _##field.isSome()                                                                                  \
         ? _##field                                                                                           \
         : getDefault<__##field##_default>();                                                                 \
  }                                                                                                           \
                                                                                                              \
public:                                                                                                       \
  Self field(typename BuilderInitializer<ty>::Type field)                                                     \
  {                                                                                                           \
    _##field = Option<ty>(std::move(field));                                                                  \
    return std::move(*this);                                                                                  \
  }                                                                                                           \
  struct __ ## field ## _default { using Type = ty; };                                                        \
                                                                                                              \
                                                                                                              \

#define TERM_INDEX_TEST_SET_DEFAULT(field, val)                                                               \
  template<> struct Test::DefaultValue<TermIndex::TestCase::__##field##_default>                              \
  {                                                                                                           \
    using Type = typename TermIndex::TestCase::__##field##_default::Type;                                     \
    static Option<Type> value()                                                                               \
    { return Option<Type>(val); }                                                                             \
  }                                                                                                           \

template<class Field>
Option<typename Field::Type> getDefault()
{ return DefaultValue<Field>::value(); }

namespace TermIndex {

using Kernel::TermList;
using Indexing::TermIndex;
class TestCase;

struct SubsElem 
{
  TermList var;
  TermList replace;
  friend std::ostream& operator<<(std::ostream& out, SubsElem const& self) 
  { return out << self.var << " -> " << self.replace; }
};

SubsElem subs(TermList var, TermList replace) 
{ return SubsElem { .var = var, .replace = replace }; }

class TermQueryResultPattern 
{
  BUILDER_METHOD(TermQueryResultPattern, TermList, term)
  BUILDER_METHOD(TermQueryResultPattern, Literal*, literal)
  BUILDER_METHOD(TermQueryResultPattern, Stack<Lit>, clause)
  BUILDER_METHOD(TermQueryResultPattern, Stack<SubsElem>, substitution)
  BUILDER_METHOD(TermQueryResultPattern, Stack<Literal*>, constraints)
public:
  bool matches(TestCase const& test, TermQueryResult& res) const;
  friend std::ostream& operator<<(std::ostream& out, TermQueryResultPattern const& self) 
  {
    out << "termQueryResult(";
    if (self.        term().isSome()) out <<    "term: " << pretty(             self.term().unwrap()) << ", ";
    if (self.     literal().isSome()) out << "literal: " << pretty(          self.literal().unwrap()) << ", ";
    if (self.      clause().isSome()) out <<  "clause: " << pretty(::clause(  self.clause().unwrap())) << ", ";
    if (self.substitution().isSome()) out <<  "clause: " << pretty(     self.substitution().unwrap()) << ", ";
    if (self. constraints().isSome()) out <<  "clause: " << pretty(      self.constraints().unwrap()) << ", ";
    out << ")";
    return out;
  }
};

TermQueryResultPattern termQueryResult()
{ return TermQueryResultPattern(); }


class TestCase
{
  using Clause = Kernel::Clause;

  BUILDER_METHOD(TestCase, TermIndex*, index)
  BUILDER_METHOD(TestCase, Stack<Clause*>, contents)
  BUILDER_METHOD(TestCase, TermList, query)
  BUILDER_METHOD(TestCase, Stack<TermQueryResultPattern>, expected)
  BUILDER_METHOD(TestCase, bool, withConstraints)

  template<class Is, class Expected>
  void testFail(Is const& is, Expected const& expected) const
  {
      cout  << endl;
      cout << "[    query ]: " << pretty(query().unwrap()) << endl;
      cout << "[ contents ]: " << pretty(contents().unwrap()) << endl;
      cout << "[       is ]: " << pretty(is) << endl;
      cout << "[ expected ]: " << pretty(expected) << endl;
      exit(-1);
  }

  bool eq(TermQueryResult& res, TermList lhs, TermList rhs)  const
  { return lhs == rhs; }

  bool eq(TermQueryResult& res, Stack<Lit> lhs, Clause* rhs)  const
  { return TestUtils::eqModAC(clause(lhs), rhs); }

  bool eq(TermQueryResult& res, Literal* lhs, Literal* rhs)  const
  { return TestUtils::eqModAC(lhs, rhs); }

  bool eq(TermQueryResult& res, Lib::Stack<Test::TermIndex::SubsElem> const& lhs, Indexing::ResultSubstitutionSP const& rhs) const
  { 
    // if (lhs.size() != rhs->size()) {
    //   return false;
    // }
    for (auto& x : lhs) {
      if (!eq(res, rhs->applyToQuery(x.var), x.replace)) 
        return false;
    }
    return true;
  }


  bool eq(TermQueryResult& res, Lib::Stack<Kernel::Literal*> const& lhs, Kernel::UnificationConstraintStackSP const& rConst) const
  { 
    if (lhs.size() != rConst->size()) return false;
    for (unsigned i = 0; i < lhs.size(); i++) {
      auto subst = [&res](pair<TermList, unsigned> const& x) 
      { return res.substitution->apply(x.first, x.second); };

      auto exp = lhs[i];
      ASS(exp->isEquality())
      auto expL = *exp->nthArgument(0);
      auto expR = *exp->nthArgument(1);

      auto& is = (*rConst)[i];
      if (!(   (eq(res, expL, subst(is.first)) && eq(res, expR, subst(is.second)) )
            || (eq(res, expL, subst(is.second)) && eq(res, expR, subst(is.first)) ))
         ) return false;
    }
    return true;
  }

  void run() 
  {

    auto index           = this->          index().unwrap();
    auto contents        = this->       contents().unwrap();
    auto query           = this->          query().unwrap();
    auto withConstraints = this->withConstraints().unwrap();
    Stack<TermQueryResultPattern> expected        = this->       expected().unwrap();

    auto container = PlainClauseContainer();
    index->attachContainer(&container);

    for (auto c : contents) {
      container.add(c);
    }

    auto results = iterTraits(withConstraints ? index->getUnificationsWithConstraints(query)
                                              : index->getUnifications(query)).collect<Stack>();

    if (results.size() != expected.size()) 
      testFail(results, expected);

    unsigned done = 0;
    for (auto& r : results) {
      auto matches = [&]() {
        for (unsigned i = done; i < expected.size(); i++) {
          if (expected[i].matches(*this, r)) {
            std::swap(expected[i], expected[done]);
            done++;
            return true;
          }
        }
        return false;
      };

      if (!matches())
        testFail(r, expected);
    }

  }
};

bool TermQueryResultPattern::matches(TestCase const& test, TermQueryResult& res) const
{
#define CHECK(field)                                                                                          \
  if (field().isSome() && !test.eq(res, field().unwrap(), res.field)) {                                       \
    return false;                                                                                             \
  }                                                                                                           \

  CHECK(term)
  CHECK(literal)
  CHECK(clause)
  CHECK(substitution)
  CHECK(constraints)
  return true;
}

#define TEST_TERM_INDEX_WITH_SUGAR(name, syntax_sugar, ...)                                                   \
  TEST_FUN(name) {                                                                                            \
    __ALLOW_UNUSED(syntax_sugar)                                                                              \
    auto test = __VA_ARGS__;                                                                                  \
    test.run();                                                                                               \
  }                                                                                                           \

#define TEST_TERM_INDEX(name, ...)                                                                            \
        TEST_TERM_INDEX_WITH_SUGAR(name, MY_SYNTAX_SUGAR, __VA_ARGS__) 

} // namespace Simplification

} // namespace Test

#endif // __TEST__GENERATION_TESTER_HPP__

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

#include "Test/TestUtils.hpp"
#include "Kernel/Clause.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Indexing/TermIndex.hpp"
#include "Test/BuilderPattern.hpp"

namespace Test {

namespace TermIndexTest {

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
    if (self.        term().isSome()) out <<    "term: " << pretty(              self.term().unwrap()) << ", ";
    if (self.     literal().isSome()) out << "literal: " << pretty(           self.literal().unwrap()) << ", ";
    if (self.      clause().isSome()) out <<  "clause: " << pretty(::clause(  self.clause().unwrap())) << ", ";
    if (self.substitution().isSome()) out <<   "subst: " << pretty(      self.substitution().unwrap()) << ", ";
    if (self. constraints().isSome()) out <<  "constr: " << pretty(       self.constraints().unwrap()) << ", ";
    out << ")";
    return out;
  }
};

TermQueryResultPattern termQueryResult()
{ return TermQueryResultPattern(); }


template<class Iter>
class IterPrinter {
  mutable Iter _iter;
public: 
  IterPrinter(Iter iter) : _iter(std::move(iter)) {}
  friend std::ostream& operator<<(std::ostream& out, IterPrinter const& self) 
  { 
    out << "iter[ ";
    if (self._iter.hasNext()) 
      out << self._iter.next();
    while(self._iter.hasNext()) 
      out << ", " << self._iter.next();
    out << " ]";
    return out;
  }
};
template<class Iter> IterPrinter<Iter> iterPrinter(Iter iter) 
{ return IterPrinter<Iter>(std::move(iter)); }

class TestCase
{
  using Clause = Kernel::Clause;

  BUILDER_METHOD(TestCase, TermIndex*, index)
  BUILDER_METHOD(TestCase, Stack<Clause*>, contents)
  BUILDER_METHOD(TestCase, TermList, query)
  BUILDER_METHOD(TestCase, Stack<TermQueryResultPattern>, expected)
  BUILDER_METHOD(TestCase, bool, withConstraints)

  template<class Is, class Expected>
  void testFail(TermIndex* index, Is const& is, Expected const& expected) const
  {
      cout  << endl;
      cout << "[    query ]: " << pretty(query().unwrap()) << endl;
      cout << "[ contents ]: " << pretty(contents().unwrap()) << endl;
      // cout << "[    index ]: " << pretty(*index) << endl;
      cout << "[       is ]: " << pretty(is) << endl;
      cout << "[ expected ]: " << pretty(expected) << endl;
      exit(-1);
  }

  bool eq(TermQueryResult& res, TermList lhs, TermList rhs)  const
  { return TestUtils::eqModAC(lhs,rhs); }

  bool eq(TermQueryResult& res, Stack<Lit> lhs, Clause* rhs)  const
  { return TestUtils::eqModAC(clause(lhs), rhs); }

  bool eq(TermQueryResult& res, Literal* lhs, Literal* rhs)  const
  { return TestUtils::eqModAC(lhs, rhs); }

  bool eq(TermQueryResult& res, Lib::Stack<SubsElem> const& lhs, Indexing::ResultSubstitutionSP const& rhs) const
  { 
    for (auto& x : lhs) {
      auto appl = rhs->applyToQuery(x.var);
      if (!eq(res, appl, x.replace)) 
        return false;
    }
    return true;
  }


  bool eq(TermQueryResult& res, Lib::Stack<Kernel::Literal*> const& lhs, Kernel::UnificationConstraintStackSP const& rConst) const
  { 
    if (!rConst) return lhs.size() == 0;
    if (lhs.size() != rConst->size()) return false;
    for (unsigned i = 0; i < lhs.size(); i++) {
      auto subst = [&](pair<TermList, unsigned> const& x) 
      { return res.substitution->applyTo(x.first, x.second); };

      auto exp = lhs[i];
      auto& is = (*rConst)[i];

      auto const_eq = [&](TermList queryPart, TermList resultPart) -> bool {
        auto expQ = res.substitution->applyToResult(resultPart);
        auto expR = res.substitution->applyToQuery(queryPart);
        return eq(res, expR, subst(is.first)) && eq(res, expQ, subst(is.second));
      };

      if (!(const_eq(*exp->nthArgument(1), *exp->nthArgument(0)) 
         || const_eq(*exp->nthArgument(0), *exp->nthArgument(1)) )) {
        return false;
      }
    }
    return true;
  }

  void run() 
  {

#define UNWRAP(field)                                                                                         \
      this->field().isNone()                                                                                  \
        ? throw UserErrorException(#field " must be specified for a valid TermIndex test case")               \
        : this->field().unwrap()

    auto index           = UNWRAP(index);
    auto contents        = UNWRAP(contents);
    auto query           = UNWRAP(query);
    auto withConstraints = UNWRAP(withConstraints);

    Stack<TermQueryResultPattern> expected        = this->expected().unwrap();

    auto container = PlainClauseContainer();
    index->attachContainer(&container);

    for (auto c : contents) {
      container.add(c);
    }

    auto results = withConstraints ? index->getUnificationsWithConstraints(query)
                                   : index->getUnifications(query);

    unsigned done = 0;
    while (results.hasNext() && done < expected.size()) {
      auto r = results.next();
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

      if (!matches()) { testFail(index, r, expected); }
    }

    if (done < expected.size() || results.hasNext()) {
      auto iter = withConstraints ? index->getUnificationsWithConstraints(query)
                                  : index->getUnifications(query);
      testFail(index, iterPrinter(iter), expected);
    }

#undef UNWRAP
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

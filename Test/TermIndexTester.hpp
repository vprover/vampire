/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __TEST__TERMINDEX_TESTER_HPP__
#define __TEST__TERMINDEX_TESTER_HPP__

// #include "Debug/Assertion.hpp"
#include "Test/TestUtils.hpp"
#include "Indexing/TermSubstitutionTree.hpp"
#include "Indexing/LiteralSubstitutionTree.hpp"

namespace Test::TermIndexTest {

using namespace Indexing;

template<class Idx, class Data, class Iter, class Key>
void perform_check(const char* operation, Idx& tree, Key key, const Stack<Data>& expected, Iter iter)
{
  auto is = iterTraits(iter(key))
    .map([](auto u) { return *u.data; })
    .template collect<Stack>();
  std::sort(is.begin(), is.end());
  std::sort(expected.begin(), expected.end());
  if (is == expected) {
    std::cout << "[  ok  ] " << operation << " " << pretty(key) << std::endl;
  } else {
    std::cout << std::endl;
    std::cout << "[ FAIL ] " << operation << " " << pretty(key) << std::endl;
    std::cout << "[  idx ] " << Output::multiline(tree) << std::endl;
    std::cout << "[  key ] " << pretty(key) << std::endl;
    std::cout << "[   is ]" << is << std::endl;
    std::cout << "[  exp ]" << expected << std::endl;
    ASSERTION_VIOLATION
  }
}

template<class Data, class Iter>
void check_lit(const char* op, LiteralSubstitutionTree<Data>& tree, Literal* key, const Stack<Data>& expected, Iter iter)
{
  auto ckey = Literal::complementaryLiteral(key);
  perform_check(op, tree,  key, expected, [&iter](auto key) { return iter(key, /* complementary */ false); });
  perform_check(op, tree, ckey, expected, [&iter](auto key) { return iter(key, /* complementary */ true); });
}

template<class Data>
void check_unify(LiteralSubstitutionTree<Data>& tree, Literal* key, const Stack<Data>& expected)
{ return check_lit("unify", tree, key, expected, [&tree](Literal* key, bool complementary)
      { return tree.getUnifications(key, complementary, /* retrieveSubstitutions */ true); }); }

template<class Data>
void check_inst(LiteralSubstitutionTree<Data>& tree, Literal* key, const Stack<Data>& expected)
{ return check_lit("getInst", tree, key, expected, [&tree](Literal* key, bool complementary)
      { return tree.getInstances(key, complementary, /* retrieveSubstitutions */ true); }); }

template<class Data>
void check_gen(LiteralSubstitutionTree<Data>& tree, Literal* key, const Stack<Data>& expected)
{ return check_lit("getGen", tree, key, expected, [&tree](Literal* key, bool complementary)
      { return tree.getGeneralizations(key, complementary, /* retrieveSubstitutions */ true); }); }


template<class Data>
void check_unify(TermSubstitutionTree<Data>& tree, TypedTermList key, const Stack<Data>& expected)
{ return perform_check("unify", tree, key, expected, [&tree](TypedTermList key)
      { return tree.getUnifications(key, /* retrieveSubstitutions */ true); }); }

// TODO write tests using this
template<class Data>
void check_gen(TermSubstitutionTree<Data>& tree, TypedTermList key, const Stack<Data>& expected)
{ return perform_check("getGen", tree, key, expected, [&tree](TypedTermList key)
      { return tree.getGeneralizations(key, /* retrieveSubstitutions */ true); }); }

// TODO write tests using this
template<class Data>
void check_inst(TermSubstitutionTree<Data>& tree, TypedTermList key, const Stack<Data>& expected)
{ return perform_check("getInst", tree, key, expected, [&tree](TypedTermList key)
      { return tree.getInstances(key, /* retrieveSubstitutions */ true); }); }

} // namespace Test::TermIndexTest

#endif // __TEST__TERMINDEX_TESTER_HPP__

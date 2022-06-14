/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Indexing/TermSubstitutionTree.hpp"

using namespace Indexing;

template<class... A>
void perform_test(const A&...) 
{ /* dummy function to get rid of warnings */ }

template<class Data>
void check_leafdata(TermSubstitutionTree<Data>& tree, TermList key, Stack<Data> expected)
{
  auto is = iterTraits(tree.getUnifications(key, /*subst */ true))
    .map([](auto u) { return u.data(); })
    .template collect<Stack>();
  std::sort(is.begin(), is.end());
  std::sort(expected.begin(), expected.end());
  if (is == expected) {
    std::cout << "[  ok  ] " << key << std::endl;
  } else {
    std::cout << "[ fail ] " << key << std::endl;
    std::cout << "[   is ]" << is << std::endl;
    std::cout << "[  exp ]" << expected << std::endl;
    ASSERTION_VIOLATION
  }
}


TEST_FUN(basic01) {

  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_CONST(b, srt)
  DECL_CONST(c, srt)
  DECL_FUNC(f, {srt}, srt)
  DECL_PRED(p, {srt})
  
  TermSubstitutionTree<> tree;
  tree.insert(f(a), DefaultLeafData(nullptr, p(a)));
  tree.insert(f(a), DefaultLeafData(nullptr, p(b)));
  tree.insert(f(a), DefaultLeafData(nullptr, p(c)));

  check_leafdata(tree, f(a), { DefaultLeafData(nullptr, p(a)), DefaultLeafData(nullptr, p(b)), DefaultLeafData(nullptr, p(c)), });
  check_leafdata(tree, f(b), Stack<DefaultLeafData>{});
  check_leafdata(tree, f(x), { DefaultLeafData(nullptr, p(a)), DefaultLeafData(nullptr, p(b)), DefaultLeafData(nullptr, p(c)), });
}

// TEST_FUN(custom_data) {
//
//   DECL_DEFAULT_VARS
//   DECL_SORT(srt)
//   DECL_CONST(a, srt)
//   DECL_CONST(b, srt)
//   DECL_FUNC(f, {srt}, srt)
//
//   TermSubstitutionTree<vstring> tree;
//   tree.insert(f(a), "a");
//   tree.insert(f(a), "b");
//   tree.insert(f(a), "c");
//
//   check_leafdata(tree, f(a), { "a", "b", "c" });
//   check_leafdata(tree, f(b), Stack<vstring>{});
//   check_leafdata(tree, f(x), { "a", "b", "c" });
// }

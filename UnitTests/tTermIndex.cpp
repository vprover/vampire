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
  DECL_PRED(g, {srt})
  
  TermSubstitutionTree<> tree;
  auto dat = [](TermList k, Literal* v)  { return DefaultLeafData(k, v, nullptr); };
  tree.insert(f(a), dat(f(a), g(a)));
  tree.insert(f(a), dat(f(a), g(b)));
  tree.insert(f(a), dat(f(a), g(c)));

  check_leafdata(tree, f(a), { dat(f(a), g(a)), dat(f(a), g(b)), dat(f(a), g(c)), });
  check_leafdata(tree, f(b), Stack<DefaultLeafData>{});
  check_leafdata(tree, f(x), { dat(f(a), g(a)), dat(f(a), g(b)), dat(f(a), g(c)), });
}

struct MyData {
  TermList term;
  vstring str;
  auto toTuple() const 
  { return std::tie(term, str); }

  friend bool operator==(MyData const& l, MyData const& r)
  { return l.toTuple() == r.toTuple(); }

  friend bool operator!=(MyData const& l, MyData const& r)
  { return !(l == r); }

  friend bool operator<(MyData const& l, MyData const& r)
  { return l.toTuple() < r.toTuple(); }

  friend bool operator> (MyData const& l, MyData const& r) { return r < l; }
  friend bool operator<=(MyData const& l, MyData const& r) { return l == r || l < r; }
  friend bool operator>=(MyData const& l, MyData const& r) { return l == r || l > r; }

  friend std::ostream& operator<<(std::ostream& out, MyData const& self)
  { return out << "MyData" << self.toTuple(); }

  TermList sort()
  { return SortHelper::getResultSort(term.term()); }
  using Key = TermList;
  Key const& key() const
  { return term; }
};


TEST_FUN(custom_data) {

  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_CONST(b, srt)
  DECL_FUNC(f, {srt}, srt)

  TermSubstitutionTree<MyData> tree;
  tree.insert(f(a), {f(a), "a"});
  tree.insert(f(a), {f(a), "b"});
  tree.insert(f(a), {f(a), "c"});

  check_leafdata(tree, f(a), { {f(a), "a"}, {f(a), "b"}, {f(a), "c"} });
  check_leafdata(tree, f(b), Stack<MyData>{});
  check_leafdata(tree, f(x), { {f(a), "a"}, {f(a), "b"}, {f(a), "c"} });
}

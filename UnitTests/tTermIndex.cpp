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
    std::cout << std::endl;
    std::cout << "[ FAIL ] " << key << std::endl;
    std::cout << "[  idx ] " << multiline(tree) << std::endl;
    std::cout << "[  key ] " << key << std::endl;
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
  
  TermSubstitutionTree<> tree(/* mismatchHandler */ nullptr);
  auto dat = [](TermList k, Literal* v)  { return DefaultTermLeafData(k, v, nullptr); };
  tree.insert(dat(f(a), g(a)));
  tree.insert(dat(f(a), g(b)));
  tree.insert(dat(f(a), g(c)));

  check_leafdata(tree, f(a), { dat(f(a), g(a)), dat(f(a), g(b)), dat(f(a), g(c)), });
  check_leafdata(tree, f(b), Stack<DefaultTermLeafData>{});
  check_leafdata(tree, f(x), { dat(f(a), g(a)), dat(f(a), g(b)), dat(f(a), g(c)), });
}

struct MyData {
  TermList term;
  vstring str;

  MyData(TermList t, vstring s)
    : term(t), str(s) {}

  TermList sort() const { return SortHelper::getResultSort(term.term()); }

  auto asTuple() const 
  { return std::tie(term, str); }

  IMPL_COMPARISONS_FROM_TUPLE(MyData)

  friend std::ostream& operator<<(std::ostream& out, MyData const& self)
  { return out << "MyData" << self.asTuple(); }

  using Key = TermList;

  Key const& key() const
  { return term; }
};


TEST_FUN(custom_data_01) {

  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_CONST(b, srt)
  DECL_FUNC(f, {srt}, srt)

  auto dat = [](auto l, auto r) { return MyData(l,r); };
  TermSubstitutionTree<MyData> tree(/* mismatchHandler */ nullptr);
  tree.insert(dat(f(a), "a"));
  tree.insert(dat(f(a), "b"));
  tree.insert(dat(f(a), "c"));

  check_leafdata(tree, f(a), { dat(f(a), "a"), dat(f(a), "b"), dat(f(a), "c") });
  check_leafdata(tree, f(b), Stack<MyData>{});
  check_leafdata(tree, f(x), { dat(f(a), "a"), dat(f(a), "b"), dat(f(a), "c") });
}

TEST_FUN(custom_data_02) {

  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_CONST(b, srt)
  DECL_FUNC(f, {srt}, srt)

  TermSubstitutionTree<TermIndexData<vstring>> tree(/* mismatchHandler */ nullptr);
  auto dat = [](TermList t,vstring s) { return TermIndexData<vstring>(t.term(), std::move(s)); };
  tree.insert(dat(f(a), "a"));
  tree.insert(dat(f(a), "b"));
  tree.insert(dat(f(a), "c"));

  check_leafdata(tree, f(a), { dat(f(a), "a"), dat(f(a), "b"), dat(f(a), "c") });
  check_leafdata(tree, f(b), Stack<TermIndexData<vstring>>{});
  check_leafdata(tree, f(x), { dat(f(a), "a"), dat(f(a), "b"), dat(f(a), "c") });
}

struct MyData3 : public MyData {
  MyData3()  = delete;
  MyData3(TermList t, vstring s) : MyData{t,s} {}
};

TEST_FUN(custom_data_03_no_default_constructor) {

  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_CONST(b, srt)
  DECL_FUNC(f, {srt}, srt)

  TermSubstitutionTree<MyData3> tree(/* mismatchHandler */ nullptr);
  auto dat = [](TermList t,vstring s) { return MyData3(t, std::move(s)); };
  tree.insert(dat(f(a), "a"));
  tree.insert(dat(f(a), "b"));
  tree.insert(dat(f(a), "c"));

  check_leafdata(tree, f(a), { dat(f(a), "a"), dat(f(a), "b"), dat(f(a), "c") });
  check_leafdata(tree, f(b), Stack<MyData3>{});
  check_leafdata(tree, f(x), { dat(f(a), "a"), dat(f(a), "b"), dat(f(a), "c") });
}

struct MyData4 : public MyData {
  MyData4(MyData const&) = delete;
  MyData4 operator=(MyData const&) = delete;
  MyData4(TermList t, vstring s) : MyData{t,s} {}
};

TEST_FUN(custom_data_04_no_copy_constructor) {

  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_CONST(b, srt)
  DECL_FUNC(f, {srt}, srt)

  TermSubstitutionTree<MyData4> tree(/* mismatchHandler */ nullptr);
  auto dat = [](TermList t,vstring s) { return MyData4(t, std::move(s)); };
  tree.insert(dat(f(a), "a"));
  tree.insert(dat(f(a), "b"));
  tree.insert(dat(f(a), "c"));

  check_leafdata(tree, f(a), { dat(f(a), "a"), dat(f(a), "b"), dat(f(a), "c") });
  check_leafdata(tree, f(b), Stack<MyData4>{});
  check_leafdata(tree, f(x), { dat(f(a), "a"), dat(f(a), "b"), dat(f(a), "c") });

  tree.remove(dat(f(a), "a"));
  tree.remove(dat(f(a), "b"));

  check_leafdata(tree, f(a), { dat(f(a), "c") });
  check_leafdata(tree, f(b), Stack<MyData4>{});
  check_leafdata(tree, f(x), { dat(f(a), "c") });
}

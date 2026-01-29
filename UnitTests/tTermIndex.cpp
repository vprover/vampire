/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Lib/DArray.hpp"

#include "Test/UnitTesting.hpp"

#include "Test/SyntaxSugar.hpp"
#include "Test/TermIndexTester.hpp"
#include "Indexing/TermSubstitutionTree.hpp"
#include "Indexing/LiteralSubstitutionTree.hpp"

using namespace Test;
using namespace Indexing;
using namespace Test::TermIndexTest;

TEST_FUN(basic01) {

  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_CONST(b, srt)
  DECL_CONST(c, srt)
  DECL_FUNC(f, {srt}, srt)
  DECL_PRED(g, {srt})
  
  TermSubstitutionTree<TermWithValue<Literal*>> tree;
  auto dat = [](TypedTermList k, Literal* v)  { return TermWithValue<Literal*>(k, v); };
  tree.insert(dat(f(a), g(a)));
  tree.insert(dat(f(a), g(b)));
  tree.insert(dat(f(a), g(c)));

  std::cout << std::endl;
  check_unify(tree, f(a), { dat(f(a), g(a)), dat(f(a), g(b)), dat(f(a), g(c)), });
  check_unify(tree, f(b), Stack<TermWithValue<Literal*>>{});
  check_unify(tree, f(x), { dat(f(a), g(a)), dat(f(a), g(b)), dat(f(a), g(c)), });
}

template<class Key>
struct MyData {
  Key term;
  std::string str;

  MyData(Key t, std::string s)
    : term(t), str(s) {}

  auto asTuple() const 
  { return std::tie(term, str); }

  IMPL_COMPARISONS_FROM_TUPLE(MyData)

  friend std::ostream& operator<<(std::ostream& out, MyData const& self)
  { return out << "MyData" << self.asTuple(); }

  Key const& key() const
  { return term; }
};



TEST_FUN(custom_data_01) {

  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_CONST(b, srt)
  DECL_FUNC(f, {srt}, srt)

  auto dat = [](auto l, auto r) { return MyData<TypedTermList>(l,r); };
  TermSubstitutionTree<MyData<TypedTermList>> tree;
  tree.insert(dat(f(a), "a"));
  tree.insert(dat(f(a), "b"));
  tree.insert(dat(f(a), "c"));

  std::cout << std::endl;
  check_unify(tree, f(a), { dat(f(a), "a"), dat(f(a), "b"), dat(f(a), "c") });
  check_unify(tree, f(b), Stack<MyData<TypedTermList>>{});
  check_unify(tree, f(x), { dat(f(a), "a"), dat(f(a), "b"), dat(f(a), "c") });
}


TEST_FUN(custom_data_literal_01) {

  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_CONST(b, srt)
  DECL_PRED(p, {srt})

  auto dat = [](Literal* l, auto r) { return MyData<Literal*>(l,r); };
  LiteralSubstitutionTree<MyData<Literal*>> tree;
  tree.insert(dat( p(a), "a"));
  tree.insert(dat(~p(a), "b"));
  tree.insert(dat( p(a), "c"));

  std::cout << std::endl;
  check_unify(tree,  p(a), { dat(p(a), "a"), dat(p(a), "c") });
  check_unify(tree, ~p(a), { dat(~p(a), "b") });
  check_unify(tree,  p(b), Stack<MyData<Literal*>>{});
  check_unify(tree, ~p(b), Stack<MyData<Literal*>>{});
  check_unify(tree,  p(x), { dat( p(a), "a"), dat(p(a), "c") });
  check_unify(tree, ~p(x), { dat(~p(a), "b") });
}

TEST_FUN(custom_data_02) {

  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_CONST(b, srt)
  DECL_FUNC(f, {srt}, srt)

  TermSubstitutionTree<TermWithValue<std::string>> tree;
  auto dat = [](TermList t,std::string s) { return TermWithValue<std::string>(t.term(), std::move(s)); };
  tree.insert(dat(f(a), "a"));
  tree.insert(dat(f(a), "b"));
  tree.insert(dat(f(a), "c"));

  std::cout << std::endl;
  check_unify(tree, f(a), { dat(f(a), "a"), dat(f(a), "b"), dat(f(a), "c") });
  check_unify(tree, f(b), Stack<TermWithValue<std::string>>{});
  check_unify(tree, f(x), { dat(f(a), "a"), dat(f(a), "b"), dat(f(a), "c") });
}

struct MyData3 : public MyData<TypedTermList> {
  MyData3()  = delete;
  MyData3(TypedTermList t, std::string s) : MyData{t,s} {}
};

TEST_FUN(custom_data_03_no_default_constructor) {

  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_CONST(b, srt)
  DECL_FUNC(f, {srt}, srt)

  TermSubstitutionTree<MyData3> tree;
  auto dat = [](TypedTermList t,std::string s) { return MyData3(t, std::move(s)); };
  tree.insert(dat(f(a), "a"));
  tree.insert(dat(f(a), "b"));
  tree.insert(dat(f(a), "c"));

  std::cout << std::endl;
  check_unify(tree, f(a), { dat(f(a), "a"), dat(f(a), "b"), dat(f(a), "c") });
  check_unify(tree, f(b), Stack<MyData3>{});
  check_unify(tree, f(x), { dat(f(a), "a"), dat(f(a), "b"), dat(f(a), "c") });
}

struct MyData4 : public MyData<TypedTermList> {
  MyData4(MyData const&) = delete;
  MyData4 operator=(MyData const&) = delete;
  MyData4(TypedTermList t, std::string s) : MyData{t,s} {}
};

TEST_FUN(custom_data_04_no_copy_constructor) {

  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_CONST(b, srt)
  DECL_FUNC(f, {srt}, srt)

  TermSubstitutionTree<MyData4> tree;
  auto dat = [](TypedTermList t,std::string s) { return MyData4(t, std::move(s)); };
  tree.insert(dat(f(a), "a"));
  tree.insert(dat(f(a), "b"));
  tree.insert(dat(f(a), "c"));

  std::cout << std::endl;
  check_unify(tree, f(a), { dat(f(a), "a"), dat(f(a), "b"), dat(f(a), "c") });
  check_unify(tree, f(b), Stack<MyData4>{});
  check_unify(tree, f(x), { dat(f(a), "a"), dat(f(a), "b"), dat(f(a), "c") });

  tree.remove(dat(f(a), "a"));
  tree.remove(dat(f(a), "b"));

  check_unify(tree, f(a), { dat(f(a), "c") });
  check_unify(tree, f(b), Stack<MyData4>{});
  check_unify(tree, f(x), { dat(f(a), "c") });
}


TEST_FUN(zero_arity_predicate) {

  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_CONST(b, srt)
  DECL_PRED(p0, {})
  DECL_PRED(p1, {srt})

  using Data = MyData<Literal*>;
  LiteralSubstitutionTree<Data> tree;
  auto dat = [](Literal* k,std::string s) { return Data(k, std::move(s)); };
  tree.insert(dat( p0() , " p0()"));
  tree.insert(dat( p1(a), " p1(a)"));
  tree.insert(dat( p1(b), " p1(b)"));
  tree.insert(dat(~p0() , "~p0()"));
  tree.insert(dat(~p1(a), "~p1(a)"));
  tree.insert(dat(~p1(b), "~p1(b)"));

  std::cout << std::endl;
  check_unify(tree,  p0() , { dat( p0() , " p0()") });
  check_unify(tree,  p1(x), { dat( p1(a), " p1(a)"), dat( p1(b), " p1(b)") });
  check_unify(tree, ~p0() , { dat(~p0() , "~p0()") });
  check_unify(tree, ~p1(x), { dat(~p1(a), "~p1(a)"), dat(~p1(b), "~p1(b)") });
  check_unify(tree,  p1(a), { dat( p1(a), " p1(a)") });
  check_unify(tree, ~p1(a), { dat(~p1(a), "~p1(a)") });

  tree.remove(dat(~p1(a), "~p1(a)"));
  check_unify(tree,  p1(x), { dat( p1(a), " p1(a)"), dat( p1(b), " p1(b)") });
  check_unify(tree, ~p1(x), {                        dat(~p1(b), "~p1(b)") });
  check_inst(tree,   p1(x), { dat( p1(a), " p1(a)"), dat( p1(b), " p1(b)") });
  check_inst(tree,  ~p1(x), {                        dat(~p1(b), "~p1(b)") });

  tree.remove(dat(~p0() , "~p0()"));

  check_unify(tree,  p0() , { dat( p0() , " p0()") });
  check_unify(tree, ~p0() , Stack<Data>{});
  check_gen(tree,  p0() , { dat( p0() , " p0()") });
  check_gen(tree, ~p0() , Stack<Data>{});
  check_inst(tree,  p0() , { dat( p0() , " p0()") });
  check_inst(tree, ~p0() , Stack<Data>{});

  tree.insert(dat( p1(x), " p1(x)"));
  tree.insert(dat(~p1(x), "~p1(x)"));
  check_gen(tree,  p1(a), { dat( p1(a), " p1(a)"), dat( p1(x), " p1(x)") });
  check_gen(tree, ~p1(a), {                        dat(~p1(x), "~p1(x)") });

  check_gen(  tree, a != a, Stack<Data>{});
  check_inst( tree, a != a, Stack<Data>{});
  check_unify(tree, a != a, Stack<Data>{});
}


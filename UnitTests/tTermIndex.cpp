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
#include "Test/TestUtils.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Indexing/TermSubstitutionTree.hpp"
#include "Indexing/LiteralSubstitutionTree.hpp"


using namespace Test;
using namespace Indexing;

template<class... A>
void perform_test(const A&...) 
{ /* dummy function to get rid of warnings */ }

template<class Idx, class Data, class Iter, class Key>
void __check(const char* operation, Idx& tree, Key key, Stack<Data> expected, Iter iter)
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
    std::cout << "[  idx ] " << multiline(tree) << std::endl;
    std::cout << "[  key ] " << pretty(key) << std::endl;
    std::cout << "[   is ]" << is << std::endl;
    std::cout << "[  exp ]" << expected << std::endl;
    ASSERTION_VIOLATION
  }
}

template<class Data, class Iter>
void check_lit(const char* op, LiteralSubstitutionTree<Data>& tree, Literal* key, Stack<Data> expected, Iter iter)
{
  auto ckey = Literal::complementaryLiteral(key);
  __check(op, tree,  key, expected, [&](auto key) { return iter(key, /* complementary */ false); });
  __check(op, tree, ckey, expected, [&](auto key) { return iter(key, /* complementary */ true); });
}


template<class Data>
void check_unify(LiteralSubstitutionTree<Data>& tree, Literal* key, Stack<Data> expected)
{ return check_lit("unify", tree, key, expected, [&](Literal* key, bool complementary) 
      { return tree.getUnifications(key, complementary, /* retrieveSubstitutions */ true); }); }

template<class Data>
void check_inst(LiteralSubstitutionTree<Data>& tree, Literal* key, Stack<Data> expected)
{ return check_lit("getInst", tree, key, expected, [&](Literal* key, bool complementary) 
      { return tree.getInstances(key, complementary, /* retrieveSubstitutions */ true); }); }

template<class Data>
void check_gen(LiteralSubstitutionTree<Data>& tree, Literal* key, Stack<Data> expected)
{ return check_lit("getGen", tree, key, expected, [&](Literal* key, bool complementary) 
      { return tree.getGeneralizations(key, complementary, /* retrieveSubstitutions */ true); }); }


template<class Data>
void check_unify(TermSubstitutionTree<Data>& tree, TermList key, Stack<Data> expected)
{ return __check("unify", tree, key, expected, [&](TermList key) 
      { return tree.getUnifications(key, /* retrieveSubstitutions */ true); }); }

// TODO write tests using this
template<class Data>
void check_gen(TermSubstitutionTree<Data>& tree, TermList key, Stack<Data> expected)
{ return __check("getGen", tree, key, expected, [&](TermList key) 
      { return tree.getGeneralizations(key, /* retrieveSubstitutions */ true); }); }

// TODO write tests using this
template<class Data>
void check_inst(TermSubstitutionTree<Data>& tree, TermList key, Stack<Data> expected)
{ return __check("getInst", tree, key, expected, [&](TermList key) 
      { return tree.getInstances(key, /* retrieveSubstitutions */ true); }); }


TEST_FUN(basic01) {

  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_CONST(b, srt)
  DECL_CONST(c, srt)
  DECL_FUNC(f, {srt}, srt)
  DECL_PRED(g, {srt})
  
  TermSubstitutionTree<TermLiteralClause> tree;
  auto dat = [](TermList k, Literal* v)  { return TermLiteralClause(k, v, nullptr); };
  tree.insert(dat(f(a), g(a)));
  tree.insert(dat(f(a), g(b)));
  tree.insert(dat(f(a), g(c)));

  check_unify(tree, f(a), { dat(f(a), g(a)), dat(f(a), g(b)), dat(f(a), g(c)), });
  check_unify(tree, f(b), Stack<TermLiteralClause>{});
  check_unify(tree, f(x), { dat(f(a), g(a)), dat(f(a), g(b)), dat(f(a), g(c)), });
}

TermList getSort(TermList term) { return SortHelper::getResultSort(term.term()); }
TermList getSort(Literal* term) { return TermList::empty(); }

template<class Key>
struct MyData {
  Key term;
  vstring str;

  MyData(Key t, vstring s)
    : term(t), str(s) {}

  TermList sort() const  { return getSort(term); }

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

  auto dat = [](auto l, auto r) { return MyData<TermList>(l,r); };
  TermSubstitutionTree<MyData<TermList>> tree;
  tree.insert(dat(f(a), "a"));
  tree.insert(dat(f(a), "b"));
  tree.insert(dat(f(a), "c"));

  check_unify(tree, f(a), { dat(f(a), "a"), dat(f(a), "b"), dat(f(a), "c") });
  check_unify(tree, f(b), Stack<MyData<TermList>>{});
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

  TermSubstitutionTree<TermIndexData<vstring>> tree;
  auto dat = [](TermList t,vstring s) { return TermIndexData<vstring>(t.term(), std::move(s)); };
  tree.insert(dat(f(a), "a"));
  tree.insert(dat(f(a), "b"));
  tree.insert(dat(f(a), "c"));

  check_unify(tree, f(a), { dat(f(a), "a"), dat(f(a), "b"), dat(f(a), "c") });
  check_unify(tree, f(b), Stack<TermIndexData<vstring>>{});
  check_unify(tree, f(x), { dat(f(a), "a"), dat(f(a), "b"), dat(f(a), "c") });
}

struct MyData3 : public MyData<TermList> {
  MyData3()  = delete;
  MyData3(TermList t, vstring s) : MyData{t,s} {}
};

TEST_FUN(custom_data_03_no_default_constructor) {

  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_CONST(b, srt)
  DECL_FUNC(f, {srt}, srt)

  TermSubstitutionTree<MyData3> tree;
  auto dat = [](TermList t,vstring s) { return MyData3(t, std::move(s)); };
  tree.insert(dat(f(a), "a"));
  tree.insert(dat(f(a), "b"));
  tree.insert(dat(f(a), "c"));

  check_unify(tree, f(a), { dat(f(a), "a"), dat(f(a), "b"), dat(f(a), "c") });
  check_unify(tree, f(b), Stack<MyData3>{});
  check_unify(tree, f(x), { dat(f(a), "a"), dat(f(a), "b"), dat(f(a), "c") });
}

struct MyData4 : public MyData<TermList> {
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

  TermSubstitutionTree<MyData4> tree;
  auto dat = [](TermList t,vstring s) { return MyData4(t, std::move(s)); };
  tree.insert(dat(f(a), "a"));
  tree.insert(dat(f(a), "b"));
  tree.insert(dat(f(a), "c"));

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
  DECL_FUNC(f, {srt}, srt)
  DECL_PRED(p0, {})
  DECL_PRED(p1, {srt})

  using Data = MyData<Literal*>;
  LiteralSubstitutionTree<Data> tree;
  auto dat = [](Literal* k,vstring s) { return Data(k, std::move(s)); };
  tree.insert(dat( p0() , " p0()"));
  tree.insert(dat( p1(a), " p1(a)"));
  tree.insert(dat( p1(b), " p1(b)"));
  tree.insert(dat(~p0() , "~p0()"));
  tree.insert(dat(~p1(a), "~p1(a)"));
  tree.insert(dat(~p1(b), "~p1(b)"));

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


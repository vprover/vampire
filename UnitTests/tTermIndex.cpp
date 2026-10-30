/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include <set>

#include "Indexing/CodeTreeInterfaces.hpp"

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
    std::cout << "[  idx ] " << Output::multiline(tree) << std::endl;
    std::cout << "[  key ] " << pretty(key) << std::endl;
    std::cout << "[   is ]" << is << std::endl;
    std::cout << "[  exp ]" << expected << std::endl;
    ASSERTION_VIOLATION
  }
}

template<class Data, class Iter, class Idx>
void check_lit(const char* op, Idx& tree, Literal* key, Stack<Data> expected, Iter iter)
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
void check_gen(CodeTreeLIS<Data>& tree, Literal* key, Stack<Data> expected)
{ return check_lit("getGen", tree, key, expected, [&](Literal* key, bool complementary) 
      { return tree.getGeneralizations(key, complementary); }); }


template<class Data>
void check_unify(TermSubstitutionTree<Data>& tree, TypedTermList key, Stack<Data> expected)
{ return __check("unify", tree, key, expected, [&](TypedTermList key) 
      { return tree.getUnifications(key, /* retrieveSubstitutions */ true); }); }

// TODO write tests using this
template<class Data>
void check_gen(TermSubstitutionTree<Data>& tree, TypedTermList key, Stack<Data> expected)
{ return __check("getGen", tree, key, expected, [&](TypedTermList key) 
      { return tree.getGeneralizations(key, /* retrieveSubstitutions */ true); }); }

// TODO write tests using this
template<class Data>
void check_inst(TermSubstitutionTree<Data>& tree, TypedTermList key, Stack<Data> expected)
{ return __check("getInst", tree, key, expected, [&](TypedTermList key) 
      { return tree.getInstances(key, /* retrieveSubstitutions */ true); }); }


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
  check_inst(tree,  p0() , { dat( p0() , " p0()") });
  check_inst(tree, ~p0() , Stack<Data>{});

  tree.insert(dat( p1(x), " p1(x)"));
  tree.insert(dat(~p1(x), "~p1(x)"));

  check_inst( tree, a != a, Stack<Data>{});
  check_unify(tree, a != a, Stack<Data>{});
}

TEST_FUN(zero_arity_predicate_gen) {

  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_CONST(b, srt)
  DECL_PRED(p0, {})
  DECL_PRED(p1, {srt})

  using Data = MyData<Literal*>;
  CodeTreeLIS<Data> tree;
  auto dat = [](Literal* k,std::string s) { return Data(k, std::move(s)); };
  tree.handle(dat( p0() , " p0()"), /*insert=*/true);
  tree.handle(dat( p1(a), " p1(a)"), /*insert=*/true);
  tree.handle(dat( p1(b), " p1(b)"), /*insert=*/true);
  tree.handle(dat(~p0() , "~p0()"), /*insert=*/true);
  tree.handle(dat(~p1(a), "~p1(a)"), /*insert=*/true);
  tree.handle(dat(~p1(b), "~p1(b)"), /*insert=*/true);

  tree.handle(dat(~p1(a), "~p1(a)"), /*insert=*/false);
  tree.handle(dat(~p0() , "~p0()"), /*insert=*/false);

  check_gen(tree,  p0() , { dat( p0() , " p0()") });
  check_gen(tree, ~p0() , Stack<Data>{});

  tree.handle(dat( p1(x), " p1(x)"), /*insert=*/true);
  tree.handle(dat(~p1(x), "~p1(x)"), /*insert=*/true);

  check_gen(tree,  p1(a), { dat( p1(a), " p1(a)"), dat( p1(x), " p1(x)") });
  check_gen(tree, ~p1(a), {                        dat(~p1(x), "~p1(x)") });
  check_gen(  tree, a != a, Stack<Data>{});
}


// The substitution a code tree returns is expressed in terms of the key's variables as numbered
// by Renaming::normalizeVariables, so the code tree must number the variables of an equality
// literal (arguments, then sort) in the same order.
TEST_FUN(gen_equality_sort_variable_order) {

  DECL_DEFAULT_VARS
  DECL_DEFAULT_SORT_VARS
  DECL_SORT(A)
  DECL_SORT(B)
  DECL_CONST(a, A)
  DECL_CONST(b, B)
  // k : !>[X0,X1]: X0 > X1, so in k(alpha,beta,x) = y the sort is beta, which is not
  // the first variable met among the arguments
  DECL_POLY_FUNC(k, 2, {alpha}, beta)

  using Data = MyData<Literal*>;
  CodeTreeLIS<Data> tree;
  Literal* key = k(alpha, beta, x) == y;
  Literal* query = k(A, B, a) == b;
  tree.handle(Data(key, "k(alpha,beta,x) = y"), /*insert=*/true);

  unsigned found = 0;
  auto it = tree.getGeneralizations(query, /*complementary=*/false);
  while (it.hasNext()) {
    auto res = it.next();
    ASS_EQ(res.unifier.apply(key), query)
    found++;
  }
  ASS_EQ(found, 1u)
}

// Compares the generalizations the literal code tree finds for equalities (two-variable ones
// with various sorts, reversed ones, polymorphic ones) and predicates with MatchingUtils::match,
// and checks that the returned substitutions map the key to the query (or to its reversal).
TEST_FUN(gen_equality_agrees_with_matching_utils) {

  DECL_DEFAULT_VARS
  DECL_DEFAULT_SORT_VARS
  DECL_SORT(A)
  DECL_SORT(B)
  DECL_TYPE_CON(list, 1)
  DECL_CONST(a, A)
  DECL_CONST(b, B)
  DECL_FUNC(f, {A}, A)
  DECL_POLY_FUNC(idf, 1, {alpha}, alpha)
  DECL_POLY_FUNC(k, 2, {alpha}, beta)
  DECL_POLY_CONST(nil, 1, list(alpha))
  DECL_POLY_FUNC(cons, 1, {alpha, list(alpha)}, list(alpha))
  DECL_PRED(p, {A, A})

  Stack<Literal*> keys = {
    sorted(x, alpha) == y,
    sorted(x, A) == y,
    sorted(x, B) == y,
    sorted(x, list(alpha)) == y,
    sorted(x, list(A)) == y,
    sorted(x, list(beta)) == y,
    sorted(x, list(list(alpha))) == y,
    sorted(x, alpha) == x,
    sorted(x, alpha) != y,
    ~(sorted(x, B) == y),
    a == sorted(x, A),
    idf(alpha, x) == y,
    idf(A, x) == f(y),
    k(alpha, beta, x) == y,
    k(alpha, alpha, x) == y,
    y == k(alpha, beta, x),
    nil(alpha) == x,
    cons(alpha, x, y) == z,
    cons(alpha, x, nil(alpha)) == nil(alpha),
    f(x) == x,
    p(x, y),
    p(x, x),
  };
  Stack<Literal*> queries = {
    a == a,
    a == f(a),
    ~(a == a),
    sorted(x, A) == y,
    sorted(x, A) == x,
    sorted(x, A) != y,
    sorted(x, B) == y,
    sorted(x, alpha) == y,
    sorted(x, list(A)) == y,
    sorted(x, list(B)) == y,
    sorted(x, list(alpha)) == y,
    sorted(x, list(beta)) == y,
    sorted(x, list(list(A))) == y,
    sorted(x, list(list(alpha))) == y,
    a == sorted(x, A),
    nil(A) == nil(A),
    nil(A) == x,
    x == nil(A),
    nil(list(A)) == y,
    cons(A, a, nil(A)) == nil(A),
    nil(A) == cons(A, a, nil(A)),
    cons(A, x, y) == z,
    k(A, B, a) == b,
    b == k(A, B, a),
    y == k(A, B, x),
    k(A, A, x) == y,
    k(alpha, beta, x) == y,
    k(alpha, alpha, x) == y,
    k(list(A), list(B), x) == y,
    idf(A, a) == a,
    a == idf(A, a),
    idf(A, x) == y,
    idf(A, a) == f(a),
    f(a) == idf(A, a),
    f(x) == x,
    x == f(x),
    p(a, a),
    p(x, y),
    p(x, x),
  };

  using Data = MyData<Literal*>;
  CodeTreeLIS<Data> tree;
  for (unsigned i = 0; i < keys.size(); i++) {
    tree.handle(Data(keys[i], std::to_string(i)), /*insert=*/true);
  }

  auto reversed = [](Literal* l) {
    return Literal::createEquality(l->polarity(), *l->nthArgument(1), *l->nthArgument(0),
                                   SortHelper::getEqualityArgumentSort(l));
  };

  for (auto query : queries) {
    for (bool complementary : {false, true}) {
      Literal* target = complementary ? Literal::complementaryLiteral(query) : query;

      std::set<unsigned> found;
      auto it = tree.getGeneralizations(query, complementary);
      while (it.hasNext()) {
        auto res = it.next();
        Literal* inst = res.unifier.apply(res.data->key());
        if (inst != target && !(target->isEquality() && inst == reversed(target))) {
          std::cout << "wrong substitution: key " << *res.data->key() << " query " << *target
                    << " instance " << *inst << std::endl;
          ASSERTION_VIOLATION
        }
        found.insert(std::stoul(res.data->str));
      }

      std::set<unsigned> expected;
      for (unsigned i = 0; i < keys.size(); i++) {
        if (MatchingUtils::match(keys[i], query, complementary)) {
          expected.insert(i);
        }
      }

      if (found != expected) {
        std::cout << "query " << *query << (complementary ? " (complementary)" : "") << std::endl;
        for (auto i : found)    { if (!expected.count(i)) std::cout << "  unexpected " << *keys[i] << std::endl; }
        for (auto i : expected) { if (!found.count(i))    std::cout << "  missing    " << *keys[i] << std::endl; }
        ASSERTION_VIOLATION
      }
    }
  }
}

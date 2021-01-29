/*
 * File tIterator.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */


#include "Test/UnitTesting.hpp"
#include "Lib/Iterator.hpp"
#include "Lib/Stack.hpp"
#include "Lib/Iterator.hpp"

#define UNIT_ID Iterator
UT_CREATE;

using namespace Lib;
using namespace Iterator;

template<class T>
auto iter(Stack<T>& t) -> decltype(indexIter(t))
{ return indexIter(t); }

template<class T>
auto iter(Stack<T> const& t) -> decltype(indexIter(t))
{ return indexIter(t); }

TEST_FUN(test_collect_1) {
  auto s = Stack<int>{ 1, 2, 3 };

  // An iterator can be collected into a container type C that 
  // implements the function
  // template<class Iter> static C fromIterator(Iter);
  ASS_EQ(iter(s) | cloned() | collect<Stack<int>>(), s)
}


TEST_FUN(test_collect_2) {
  auto s = Stack<int>{ 1, 2, 3 };

  ASS_EQ(iter(s) | cloned() | collect<Stack>(), s)
}


TEST_FUN(test_range_1) {
  auto s = Stack<int>{ 1, 2, 3 };

  ASS_EQ(rangeExcl(1,4) | collect<Stack>(), s)
  ASS_EQ(rangeIncl(1,3) | collect<Stack>(), s)
}


TEST_FUN(test_range_2) {
  auto s = Stack<int>{ 1,   2, 3,
                       7,   8,
                       11, 12, 13};

  ASS_EQ(concat(rangeIncl(1,3), rangeIncl(7,8), rangeIncl(11,13)) | collect<Stack>(), s)
}



TEST_FUN(test_map_1) {
  auto in  = Stack<int>{ 1, 2, 3 };
  auto out = Stack<int>{ 2, 4, 6 };

  ASS_EQ(iter(in)
      | map([](int& i) { return 2 * i; })
      | collect<Stack<int>>(), out)
}

TEST_FUN(test_map_2) {
  auto in  = Stack<int>     { 1, 2, 3 };
  auto out = Stack<unsigned>{ 1, 2, 3 };

  ASS_EQ(iter(in)
      | map([](int i) { return (unsigned) i; })
      | collect<Stack<unsigned>>(), out)
}


TEST_FUN(test_map_3) {
  auto in  = Stack<int>    {  1,   2,   3  };
  auto out = Stack<vstring>{ "1", "2", "3" };

  ASS_EQ(iter(in)
      | map([](int i) { return (unsigned) i; })
      | map([](unsigned i) { 
          vstringstream s;
          s << i;
          return s.str(); 
        })
      | collect<Stack>(), out)
}

TEST_FUN(test_filter) {
  auto in  = Stack<int>{ 1, 2, 3, 4 };
  auto out = Stack<int>{    2,    4 };

  ASS_EQ(iter(in)
      | filter([](int const& i) { return i % 2 == 0; })
      | collect<Stack<int>>(), out)
}

TEST_FUN(test_foreach) {
  auto in  = Stack<int>{ 1, 2, 3 };
  auto out = Stack<int>{};

  iter(in)
        | foreach([&](int i) { out.push(i); });

  ASS_EQ(in, out);
}

TEST_FUN(test_for) {
  auto in  = Stack<int>{ 1, 2, 3 };
  auto out = Stack<int>{};

  for ( auto i : iter(in) ) {
    out.push(i); 
  }

  ASS_EQ(in, out);
}



TEST_FUN(test_for_const) {
  auto const in  = Stack<int>{ 1, 2, 3 };
  auto out = Stack<int>{};

  for ( auto i : iter(in) ) {
    out.push(i); 
  }

  ASS_EQ(in, out);
}


TEST_FUN(test_flatMap_1) {
  auto in  = Stack<Stack<int>>{ Stack<int>{1, 2},    
                                Stack<int>{3, 4},    
                                Stack<int>{5, 6}, };
  auto out = Stack<int>{ 1, 2, 3, 4, 5, 6, };

  ASS_EQ(iter(in)
      | map([](Stack<int> const& i) { return iter(i); })
      | flatten()
      | cloned()
      | collect<Stack>(), out)
}

TEST_FUN(test_flatMap_2) {
  auto in  = Stack<Stack<int>>{ Stack<int>{1, 2},    
                                Stack<int>{3, 4},    
                                Stack<int>{5, 6}, };
  auto out = Stack<int>{ 1, 2, 3, 4, 5, 6, };

  ASS_EQ(iter(in)
      | flatMap([](Stack<int> const& i) { return iter(i); })
      | cloned()
      | collect<Stack>(), out)
}


/** non-copyable iterator */
class OwnedStackIter : public Iterator::Iterators::IndexIter<Stack<int>, unsigned> {
public:
  DECL_ELEMENT_TYPE(ElemT<IndexIter<Stack<int>>>);

  OwnedStackIter(Stack<int> stack) : IndexIter<Stack<int>>(std::move(stack)) {}
  OwnedStackIter(OwnedStackIter &&) = default;
  OwnedStackIter(OwnedStackIter const&) = delete;
  OwnedStackIter& operator=(OwnedStackIter const&) = delete;
  OwnedStackIter& operator=(OwnedStackIter &&) = default;
  using IndexIter<Stack<int>>::next;
  using IndexIter<Stack<int>>::sizeLeft;
};

TEST_FUN(test_flatMap_3) {
  auto in  = Stack<int>{ 1, 3, 5, };
  auto out = Stack<int>{ 1, 2, 3, 4, 5, 6, };

  ASS_EQ(iter(in)
      | flatMap([](int i) -> OwnedStackIter { return OwnedStackIter(Stack<int>{i, i + 1}); })
      | cloned()
      | collect<Stack<int>>(), out)
}

TEST_FUN(test_flatMap_4) {
  auto in  = Stack<int>{ 1, 3, 5, };
  auto out = Stack<int>{ 1, 2, 3, 4, 5, 6, };

  ASS_EQ(iter(in)
      | flatMap([](int& i) { return OwnedStackIter(Stack<int>{i, i + 1}); })
      | sizeHint(6)
      | cloned()
      | collect<Stack>(), out)
}

TEST_FUN(test_all_1) {
  auto in  = Stack<int>{ 1, 3, 5, };

  ASS(iter(in) | all([](int i) { return i % 2 == 1; }))
}

TEST_FUN(test_all_2) {
  auto in  = Stack<int>{ 1, 3, 5, };

  ASS(iter(in) | !all([](int i) { return i % 2 == 0; }))
}

TEST_FUN(test_all_3) {
  auto in  = Stack<int>{ 1, 3, 6, };

  ASS(iter(in) | !all([](int i) { return i % 2 == 0; }))
}

TEST_FUN(test_any_1) {
  auto in  = Stack<int>{ 1, 3, 6, };

  ASS(iter(in) | any([](int i) { return i % 2 == 0; }))
}

TEST_FUN(test_any_2) {
  auto in  = Stack<int>{ 1, 3, 6, };

  ASS(iter(in) | any([](int i) { return i % 2 == 1; }))
}

TEST_FUN(test_any_3) {
  auto in  = Stack<int>{ 1, 3, 6, };

  ASS(iter(in) | !any([](int i) { return i < 0; }))
}

TEST_FUN(test_fold_1) {
  auto in  = Stack<int>{ 1, 2, 3, };

  ASS_EQ(6, iter(in) | fold(0, [](int i, int j) { return i + j; }))
}

TEST_FUN(test_fold_2) {
  auto in  = Stack<int>{ 1, 2, 3, };

  ASS_EQ(", odd, even, odd", 
      iter(in) | fold("", [](vstring str, int j)
        { return str + ", " + ( j % 2 == 0 ? "even" : "odd" ); }))
}

TEST_FUN(test_fold_3) {
  auto in  = Stack<int>{ 1, 2, 3, };

  ASS_EQ("odd, even, odd", 
      (iter(in) 
      | map([](int i ) -> vstring { return i % 2 == 0 ? "even" : "odd"; })
      | fold([](vstring i, vstring j) { return i + ", " + j; })).unwrap())
}

TEST_FUN(test_dyn_move_semantics_1) {
  auto in  = Stack<int>{ 1, 3, 5, };
  auto out = Stack<int>{ 1, 2, 3, 4, 5, 6, };

  ASS_EQ((iter(in)
      | map([](int i) -> DynIter<int> { return dyn(OwnedStackIter(Stack<int>{i, i + 1}) | cloned()); })
      | fold([](DynIter<int> s1, DynIter<int> s2) { return dyn(concat(std::move(s1), std::move(s2))); })).unwrap()
      | collect<Stack>(), out)
}

TEST_FUN(test_dyn_move_semantics_2) {
  auto in  = Stack<int>{ 1, 3, 5, };
  auto dynIterStack = iter(in)
      | map([](int i) { return dyn(OwnedStackIter(Stack<int>{i, i + 1}) | cloned()); })
      | collect<Stack<DynIter<int>>>();


  auto expected = Stack<int>{ 2, 2, 2 };
  ASS_EQ(expected,
        indexIter(dynIterStack)
          | map([](DynIter<int> & iter) { return iter.sizeLeft().unwrap(); } )
          | collect<Stack<int>>())
  ASS_EQ(expected,
        indexIter(dynIterStack)
          | map([](DynIter<int> & iter) { return iter.sizeLeft().unwrap(); } )
          | collect<Stack<int>>())
}


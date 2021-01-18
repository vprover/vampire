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

TEST_FUN(test_collect_1) {
  auto s = Stack<int>{ 1, 2, 3 };

  // An iterator can be collected into a container type C that 
  // implements the function
  // template<class Iter> static C fromIterator(Iter);
  ASS_EQ(s.iterFifo() | cloned() | collect<Stack<int>>(), s)
}


TEST_FUN(test_collect_2) {
  auto s = Stack<int>{ 1, 2, 3 };

  ASS_EQ(s.iterFifo() | cloned() | collect<Stack>(), s)
}


TEST_FUN(test_range_1) {
  auto s = Stack<int>{ 1, 2, 3 };

  ASS_EQ(rangeExcl(1,4) | collect<Stack>(), s)
  ASS_EQ(rangeIncl(1,3) | collect<Stack>(), s)
}



TEST_FUN(test_map_1) {
  auto in  = Stack<int>{ 1, 2, 3 };
  auto out = Stack<int>{ 2, 4, 6 };

  ASS_EQ(in.iterFifo()
      | map([](int i) { return 2 * i; })
      | collect<Stack<int>>(), out)
}

TEST_FUN(test_map_2) {
  auto in  = Stack<int>     { 1, 2, 3 };
  auto out = Stack<unsigned>{ 1, 2, 3 };

  ASS_EQ(in.iterFifo()
      | map([](int i) { return (unsigned) i; })
      | collect<Stack<unsigned>>(), out)
}


TEST_FUN(test_map_3) {
  auto in  = Stack<int>    {  1,   2,   3  };
  auto out = Stack<vstring>{ "1", "2", "3" };

  ASS_EQ(in.iterFifo()
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

  ASS_EQ(in.iterFifo()
      | filter([](int const& i) { return i % 2 == 0; })
      | collect<Stack<int>>(), out)
}

TEST_FUN(test_foreach) {
  auto in  = Stack<int>{ 1, 2, 3 };
  auto out = Stack<int>{};

  in.iterFifo()
        | forEach([&](int i) { out.push(i); });

  ASS_EQ(in, out);
}

TEST_FUN(test_for) {
  auto in  = Stack<int>{ 1, 2, 3 };
  auto out = Stack<int>{};

  for ( auto i : in.iterFifo() | toStl() ) {
    out.push(i); 
  }

  ASS_EQ(in, out);
}

TEST_FUN(test_flatMap_1) {
  auto in  = Stack<Stack<int>>{ Stack<int>{1, 2},    
                                Stack<int>{3, 4},    
                                Stack<int>{5, 6}, };
  auto out = Stack<int>{ 1, 2, 3, 4, 5, 6, };

  ASS_EQ(in.iterFifo()
      | map([](Stack<int> const& i) { return i.iterFifo(); })
      | flatten()
      | cloned()
      | collect<Stack>(), out)
}

TEST_FUN(test_flatMap_2) {
  auto in  = Stack<Stack<int>>{ Stack<int>{1, 2},    
                                Stack<int>{3, 4},    
                                Stack<int>{5, 6}, };
  auto out = Stack<int>{ 1, 2, 3, 4, 5, 6, };

  ASS_EQ(in.iterFifo()
      | flatMap([](Stack<int> const& i) { return i.iterFifo(); })
      | cloned()
      | collect<Stack>(), out)
}


/** non-copyable iterator */
class OwnedStackIter {
  Stack<int> _stack;
  unsigned _index;
public:
  DECL_ELEMENT_TYPE(int);

  OwnedStackIter(Stack<int>&& stack) : _stack(std::move(stack)), _index(0) {  }
  OwnedStackIter(Stack<int> const&) = delete;
  OwnedStackIter& operator=(Stack<int> const&) = delete;

  bool hasNext() const { return _index < _stack.size(); }
  int next() { return _stack[_index++]; }
  Option<unsigned> sizeLeft() const { return Option<unsigned>(_stack.size() - _index); }
};

TEST_FUN(test_flatMap_3) {
  auto in  = Stack<int>{ 1, 3, 5, };
  auto out = Stack<int>{ 1, 2, 3, 4, 5, 6, };

  ASS_EQ(in.iterFifo()
      | flatMap([](int i) { return OwnedStackIter(Stack<int>{i, i + 1}); })
      | collect<Stack>(), out)
}

TEST_FUN(test_flatMap_4) {
  auto in  = Stack<int>{ 1, 3, 5, };
  auto out = Stack<int>{ 1, 2, 3, 4, 5, 6, };

  ASS_EQ(in.iterFifo()
      | flatMap([](int i) { return OwnedStackIter(Stack<int>{i, i + 1}); })
      | sizeHint(6)
      | collect<Stack>(), out)
}

TEST_FUN(test_all_1) {
  auto in  = Stack<int>{ 1, 3, 5, };

  ASS(in.iterFifo() | all([](int i) { return i % 2 == 1; }))
}

TEST_FUN(test_all_2) {
  auto in  = Stack<int>{ 1, 3, 5, };

  ASS(in.iterFifo() | !all([](int i) { return i % 2 == 0; }))
}

TEST_FUN(test_all_3) {
  auto in  = Stack<int>{ 1, 3, 6, };

  ASS(in.iterFifo() | !all([](int i) { return i % 2 == 0; }))
}

TEST_FUN(test_any_1) {
  auto in  = Stack<int>{ 1, 3, 6, };

  ASS(in.iterFifo() | any([](int i) { return i % 2 == 0; }))
}

TEST_FUN(test_any_2) {
  auto in  = Stack<int>{ 1, 3, 6, };

  ASS(in.iterFifo() | any([](int i) { return i % 2 == 1; }))
}

TEST_FUN(test_any_3) {
  auto in  = Stack<int>{ 1, 3, 6, };

  ASS(in.iterFifo() | !any([](int i) { return i < 0; }))
}

TEST_FUN(test_fold_1) {
  auto in  = Stack<int>{ 1, 2, 3, };

  ASS_EQ(6, in.iterFifo() | fold(0, [](int i, int j) { return i + j; }))
}

TEST_FUN(test_fold_2) {
  auto in  = Stack<int>{ 1, 2, 3, };

  ASS_EQ(", odd, even, odd", 
      in.iterFifo() | fold("", [](vstring str, int j)
        { return str + ", " + ( j % 2 == 0 ? "even" : "odd" ); }))
}

TEST_FUN(test_fold_3) {
  auto in  = Stack<int>{ 1, 2, 3, };

  ASS_EQ("odd, even, odd", 
      (in.iterFifo() 
      | map([](int i ) -> vstring { return i % 2 == 0 ? "even" : "odd"; })
      | fold([](vstring i, vstring j) { return i + ", " + j; })).unwrap())
}

TEST_FUN(test_dyn_move_semantics_1) {
  auto in  = Stack<int>{ 1, 3, 5, };
  auto out = Stack<int>{ 1, 2, 3, 4, 5, 6, };

  ASS_EQ((in.iterFifo()
      | map([](int i) -> DynIter<int> { return dyn(OwnedStackIter(Stack<int>{i, i + 1})); })
      | fold([](DynIter<int> s1, DynIter<int> s2) { return dyn(concat(std::move(s1), std::move(s2))); })).unwrap()
      | collect<Stack>(), out)
}

TEST_FUN(test_dyn_move_semantics_2) {
  auto in  = Stack<int>{ 1, 3, 5, };
  auto dynIterStack = in.iterFifo()
      | map([](int i) { return dyn(OwnedStackIter(Stack<int>{i, i + 1})); })
      | collect<Stack<DynIter<int>>>();


  auto expected = Stack<int>{ 2, 2, 2 };
  ASS_EQ(expected,
        indexIter<Stack<DynIter<int>>&>(dynIterStack)
          | map([](DynIter<int> & iter) { return iter.sizeLeft().unwrap(); } )
          | collect<Stack<int>>())
  ASS_EQ(expected,
        indexIter<Stack<DynIter<int>>&>(dynIterStack)
          | map([](DynIter<int> & iter) { return iter.sizeLeft().unwrap(); } )
          | collect<Stack<int>>())

  // expected = Stack<int>{ 1,2,3,4,5,6 };
  // ASS_EQ(expected, 
  //        (indexIter<Stack<DynIter<int>>&>(dynIterStack)
  //         | fold([](DynIter<int>&& s1, DynIter<int>& s2) -> DynIter<int> { return dyn(concat(std::move(s1), std::move(s2))); })).unwrap()
  //         | collect<Stack<int>>())

}


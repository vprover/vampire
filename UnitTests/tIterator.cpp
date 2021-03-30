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
#include "Lib/Metaiterators.hpp"
#include "Lib/Stack.hpp"

using namespace Lib;

TEST_FUN(test_collect) {
  auto s = Stack<int>{ 1, 2, 3 };

  ASS_EQ(iterTraits(s.iterFifo()).collect<Stack<int>>(), s)
}


TEST_FUN(test_map) {
  auto in  = Stack<int>{ 1, 2, 3 };
  auto out = Stack<int>{ 2, 4, 6 };

  ASS_EQ(iterTraits(in.iterFifo())
      .map([](int i) { return 2 * i; })
      .collect<Stack<int>>(), out)
}

TEST_FUN(test_filter) {
  auto in  = Stack<int>{ 1, 2, 3, 4 };
  auto out = Stack<int>{    2,    4 };

  ASS_EQ(iterTraits(in.iterFifo())
      .filter([](int i) { return i % 2 == 0; })
      .collect<Stack<int>>(), out)
}

TEST_FUN(test_foreach) {
  auto in  = Stack<int>{ 1, 2, 3 };
  auto out = Stack<int>{};

  iterTraits(in.iterFifo())
        .forEach([&](int i) { out.push(i); });

  ASS_EQ(in, out);
}


TEST_FUN(test_for) {
  auto in  = Stack<int>{ 1, 2, 3 };
  auto out = Stack<int>{};

  for ( auto i : iterTraits(in.iterFifo())) {
    out.push(i); 
  }

  ASS_EQ(in, out);
}


TEST_FUN(testFlatMap1) {
  auto in  = Stack<Stack<int>>{ Stack<int>{1, 2},    
                                Stack<int>{3, 4},    
                                Stack<int>{5, 6}, };
  auto out = Stack<int>{ 1, 2, 3, 4, 5, 6, };

  ASS_EQ(iterTraits(in.iterFifo())
      .flatMap([](Stack<int> const& i) { return i.iterFifo(); })
      .template collect<Stack>(), out)
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
};

TEST_FUN(testFlatMap2) {
  auto in  = Stack<int>{ 1, 3, 5, };
  auto out = Stack<int>{ 1, 2, 3, 4, 5, 6, };

  ASS_EQ(iterTraits(in.iterFifo())
      .flatMap([](int i) { return OwnedStackIter(Stack<int>{i, i + 1}); })
      .template collect<Stack>(), out)
}



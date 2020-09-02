
#include "Test/UnitTesting.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Stack.hpp"

#define UNIT_ID Iterator
UT_CREATE;

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


TEST_FUN(testFlatMap) {
  auto in  = Stack<Stack<int>>{ Stack<int>{1, 2},    
                                Stack<int>{3, 4},    
                                Stack<int>{5, 6}, };
  auto out = Stack<int>{ 1, 2, 3, 4, 5, 6, };

  DBG("running")
  ASS_EQ(iterTraits(in.iterFifo())
      .flatMap([](Stack<int> const& i) { return i.iterFifo(); })
      .template collect<Stack>(), out)
}



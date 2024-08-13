/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#include "Debug/Assertion.hpp"
#include "Lib/Set.hpp"
#include "Test/UnitTesting.hpp"
#include "UnitTests/dummyHash.hpp"

using namespace Lib;

TEST_FUN(find_remove_contains)
{
  Set<int> *test_set = new Set<int>();
  int test_num = 42;
  int found_num = 0;
  test_set->insert(test_num);
  // basic `find` test
  ALWAYS(test_set->find(test_num, found_num));
  ASS_EQ(test_num, found_num);
  // basic `remove` test
  ALWAYS(test_set->remove(test_num));
  // `find` a deleted cell
  found_num = 0;
  NEVER(test_set->find(test_num, found_num));
  ASS_EQ(found_num, 0);
  // `contains` for a deleted cell
  NEVER(test_set->contains(test_num));
  // `remove` deleted
  NEVER(test_set->remove(test_num));
  // `insert` deleted
  test_set->insert(test_num);
}

TEST_FUN(reset)
{
  Set<int> *test_set = new Set<int>();
  test_set->insert(42);
  ASS_EQ(test_set->size(), 1);
  test_set->reset();
  ASS_EQ(test_set->size(), 0);
}

TEST_FUN(dummy_hash)
{
  Set<int, DummyHash> *test_set = new Set<int, DummyHash>();
  int test_num = 42;
  // two different cells fall in the same hash bucket
  test_set->insert(test_num + 1);
  test_set->insert(test_num);
  ASS_EQ(test_set->size(), 2);
  int found_num = 0;
  ALWAYS(test_set->find(test_num, found_num));
  ASS_EQ(found_num, test_num);
  ALWAYS(test_set->remove(test_num));
  ASS_EQ(test_set->size(), 1);
}

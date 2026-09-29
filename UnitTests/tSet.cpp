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
#include "Lib/Comparison.hpp"
#include "Lib/SharedSet.hpp"
#include "Lib/Environment.hpp"
#include "Indexing/TermSharing.hpp"
#include "Kernel/OperatorType.hpp"
#include "Kernel/Signature.hpp"
#include <array>
#include <sstream>
#include "Test/DummyHash.hpp"
#include "Test/UnitTesting.hpp"

TEST_FUN(find_remove_contains)
{
  Set<int, FnvHash> *test_set = new Set<int, FnvHash>();
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
  Set<int, FnvHash> *test_set = new Set<int, FnvHash>();
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

namespace {

// A call to the old hash equality interface must fail to compile.
struct HashOnlyWithCollisions {
  template<class T>
  static unsigned hash(const T&) { return 0; }
  template<class T, class U>
  static bool equals(const T&, const U&) = delete;
};

// Deliberately has no operator==.
struct SetKey { unsigned value = 0; };
struct SetProbe { unsigned value; };

std::ostream& operator<<(std::ostream& out, SetKey key)
{ return out << key.value; }

struct SetModuloEqual {
  bool operator()(SetKey lhs, SetKey rhs) const
  { return lhs.value % 256 == rhs.value % 256; }
  bool operator()(SetKey lhs, SetProbe rhs) const
  { return lhs.value % 256 == rhs.value % 256; }
};

}

TEST_FUN(defaultEqualityWithCollisionsAndResizing)
{
  Set<unsigned, HashOnlyWithCollisions> set;
  for (unsigned i = 0; i < 96; ++i) {
    ASS_EQ(set.insert(i), i);
  }
  ASS_EQ(set.size(), 96);
  for (unsigned i = 0; i < 96; ++i) {
    unsigned found = 1000;
    ALWAYS(set.find(i, found));
    ASS_EQ(found, i);
    ALWAYS(set.contains(i));
    ALWAYS(set.remove(i));
    NEVER(set.contains(i));
  }
  ASS_EQ(set.size(), 0);
  for (unsigned i = 0; i < 96; ++i) {
    ASS_EQ(set.insert(i), i);
  }
  ASS_EQ(set.size(), 96);
}

TEST_FUN(customEqualityAndHeterogeneousLookup)
{
  using CustomSet = Set<SetKey, HashOnlyWithCollisions, SetModuloEqual>;
  CustomSet set;
  for (unsigned i = 0; i < 96; ++i) {
    ASS_EQ(set.insert({i}).value, i);
  }
  for (unsigned i = 0; i < 96; ++i) {
    ASS_EQ(set.insert({i + 256}).value, i);
    ALWAYS(set.contains({i + 256}));
    SetKey found;
    ALWAYS(set.find(SetProbe{i + 512}, found));
    ASS_EQ(found.value, i);
  }
  ASS_EQ(set.size(), 96);
  for (unsigned i = 0; i < 96; i += 2) {
    ALWAYS(set.remove({i + 256}));
    NEVER(set.contains({i}));
  }
  for (unsigned i = 0; i < 96; i += 2) {
    ASS_EQ(set.insert({i + 512}).value, i + 512);
  }
  CustomSet moved(std::move(set));
  ASS_EQ(set.size(), 0);
  CustomSet swapped;
  std::swap(moved, swapped);
  ASS_EQ(moved.size(), 0);
  ASS_EQ(swapped.size(), 96);
  auto it = swapped.iter();
  unsigned count = 0;
  while (it.hasNext()) {
    auto key = it.next();
    ASS_EQ(key.value, key.value % 256 + (key.value % 2 == 0 ? 512 : 0));
    ++count;
  }
  ASS_EQ(count, 96);
  SetKey found;
  NEVER(swapped.find(SetProbe{200}, found));
  NEVER(swapped.remove({200}));
  std::ostringstream printed;
  printed << swapped;
  ASS(!printed.str().empty());
}

TEST_FUN(structuralPointerEqualityAfterResizing)
{
  std::array<int, 128> values, copies;
  Set<int*, DerefPtrHash<FnvHash>, DerefPtrEqual> set;
  for (unsigned i = 0; i < values.size(); ++i) {
    values[i] = copies[i] = i;
    ASS_EQ(set.insert(&values[i]), &values[i]);
  }
  for (unsigned i = 0; i < values.size(); ++i) {
    ASS_EQ(set.insert(&copies[i]), &values[i]);
    int* found = nullptr;
    ALWAYS(set.find(&copies[i], found));
    ASS_EQ(found, &values[i]);
  }
  ASS_EQ(set.size(), values.size());
}

TEST_FUN(sharingEqualityAfterResizing)
{
  using namespace Kernel;
  unsigned first[] = {3, 1, 3, 2};
  auto shared = SharedSet<unsigned>::getFromArray(first, 4);
  auto sort = AtomicSort::defaultSort();
  auto type = OperatorType::getFunctionType({sort}, sort);
  for (unsigned i = 0; i < 128; ++i) {
    SharedSet<unsigned>::getFromArray(&i, 1);
    OperatorType::getFunctionTypeUniformRange(i, sort, sort);
  }
  unsigned second[] = {1, 2, 3};
  ASS_EQ(SharedSet<unsigned>::getFromArray(second, 3), shared);
  ASS_EQ(OperatorType::getFunctionType({sort}, sort), type);

  auto pred = env.signature->addPredicate("set_equality_predicate",
      OperatorType::getPredicateType({sort}))->number();
  auto positive = Literal::create1(pred, true, TermList(0, false));
  auto negative = Literal::create1(pred, false, TermList(0, false));
  auto other = Literal::create1(pred, false, TermList(1, false));
  ASS_EQ(env.sharing->tryGetOpposite(positive), negative);
  ASS_EQ(env.sharing->tryGetOpposite(negative), positive);
  ASS_EQ(env.sharing->tryGetOpposite(other), nullptr);
}

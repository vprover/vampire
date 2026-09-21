/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Lib/Exception.hpp"
#include "Lib/BiMap.hpp"
#include "Lib/Hash.hpp"
#include "Lib/Map.hpp"
#include "Lib/Perfect.hpp"
#include "Kernel/BottomUpEvaluation.hpp"
#include "Test/UnitTesting.hpp"

using namespace Lib;

namespace {

// Force collisions, including Map's handling of a zero hash.
struct HashOnly {
  template<class T>
  static unsigned hash(const T&) { return 0; }
};

struct HashWithEquality : HashOnly {
  static bool equals(unsigned, unsigned) = delete;
};

// No operator==: every comparison must use the explicit predicate.
struct Key {
  unsigned value;
};

struct ModuloEqual {
  bool operator()(Key lhs, Key rhs) const { return lhs.value % 100 == rhs.value % 100; }
};

struct DerefEqual {
  bool operator()(const int* lhs, const int* rhs) const { return *lhs == *rhs; }
};

struct LongModuloEqual {
  bool operator()(long lhs, long rhs) const { return lhs % 100 == rhs % 100; }
};

}

TEST_FUN(defaultEqualityWithHashOnly)
{
  Map<unsigned, unsigned, HashOnly> map;
  for (unsigned i = 0; i < 100; ++i) {
    ASS_EQ(map.insert(i, i + 1), i + 1);
  }
  ASS_EQ(map.size(), 100);
  for (unsigned i = 0; i < 100; ++i) {
    ASS_EQ(map.insert(i, 999), i + 1);
    ASS_EQ(map.get(i), i + 1);
  }
  ASS(!map.find(100));
}

TEST_FUN(defaultEqualityIgnoresHashEquality)
{
  Map<unsigned, unsigned, HashWithEquality> map;
  map.insert(1, 10);
  map.insert(2, 20);
  ASS_EQ(map.size(), 2);
  ASS_EQ(map.get(1), 10);
  ASS_EQ(map.get(2), 20);
}

TEST_FUN(customEqualityAcrossMapOperations)
{
  Map<Key, unsigned, HashOnly, ModuloEqual> map;
  // Grow through several capacities, then look up different but equal keys.
  for (unsigned i = 0; i < 80; ++i) {
    map.insert(Key{i}, i);
  }
  const auto& constMap = map;
  for (unsigned i = 0; i < 80; ++i) {
    Key key{i + 100};
    ASS_EQ(map.insert(key, 999), i);
    ASS_EQ(map.get(key), i);
    ASS_EQ(map.tryGet(key).unwrap(), i);
    ASS_EQ(*map.getPtr(key), i);
    ASS_EQ(*constMap.getPtr(key), i);
    unsigned found = 999;
    ASS(map.find(key));
    ALWAYS(map.find(key, found));
    ASS_EQ(found, i);
  }
  ASS_EQ(map.size(), 80);
  ASS(!map.find(Key{199}));
  ASS(!map.tryGet(Key{199}).isSome());
  ASS(map.getPtr(Key{199}) == nullptr);
  ASS(constMap.getPtr(Key{199}) == nullptr);

  ALWAYS(map.replaceOrInsert(Key{101}, 201));
  ASS_EQ(map.get(Key{1}), 201);
  NEVER(map.replaceOrInsert(Key{180}, 280));
  ASS_EQ(map.get(Key{80}), 280);
  map.replace(Key{102}, 202);
  ASS_EQ(map.get(Key{2}), 202);

  unsigned initialized = 0;
  auto init = [&]() { ++initialized; return 300u; };
  auto update = [](unsigned value) { return value + 1; };
  ASS_EQ(map.getOrInit(Key{103}, init), 3);
  ASS_EQ(map.updateOrInit(Key{104}, update, init), 5);
  ASS_EQ(initialized, 0);
  ASS_EQ(map.getOrInit(Key{181}, init), 300);
  ASS_EQ(map.updateOrInit(Key{182}, update, init), 300);
  ASS_EQ(initialized, 2);

  unsigned* value = nullptr;
  NEVER(map.getValuePtr(Key{105}, value, 999));
  ASS_EQ(*value, 5);
  ALWAYS(map.getValuePtr(Key{183}, value, 383));
  ASS_EQ(*value, 383);
  ASS_EQ(map.get(Key{83}), 383);

  decltype(map) copy(map);
  ASS_EQ(copy.get(Key{201}), 201);
  decltype(map) moved(std::move(copy));
  ASS_EQ(moved.get(Key{201}), 201);
  map.reset();
  ASS(!map.find(Key{101}));
  map.insert(Key{1}, 42);
  ASS_EQ(map.get(Key{101}), 42);
}

TEST_FUN(bimapCustomEqualityInBothDirections)
{
  BiMap<const int*, long, HashOnly, HashOnly, DerefEqual, LongModuloEqual> map;
  int a = 1, equalA = 1, b = 2;
  map.insert(&a, 7L);
  ASS(map.find(&equalA));
  ASS(map.find(107L));
  ASS_EQ(map.get(&equalA), 7L);
  ASS(map.get(107L) == &a);
  ASS(map.tryGet(&equalA).isSome());
  ASS(map.tryGet(107L).isSome());
  unsigned initialized = 0;
  auto init = [&]() { ++initialized; return 8L; };
  ASS_EQ(map.getOrInit(&equalA, init), 7L);
  ASS_EQ(initialized, 0);
  ASS_EQ(map.getOrInit(&b, init), 8L);
  ASS_EQ(initialized, 1);
  ASS(map.get(108L) == &b);
  ASS_EQ(map.size(), 2);
}

TEST_FUN(memoAndUniqueForwardEquality)
{
  Memo::Hashed<Key, unsigned, HashOnly, ModuloEqual> memo;
  unsigned initialized = 0;
  auto init = [&]() { return ++initialized; };
  ASS_EQ(memo.getOrInit(Key{1}, init), 1);
  ASS_EQ(memo.getOrInit(Key{101}, init), 1);
  ASS_EQ(memo.get(Key{201}).unwrap(), 1);
  ASS(!memo.get(Key{2}).isSome());
  ASS_EQ(initialized, 1);

  Stack<Key> keys;
  keys.pushMany(Key{1}, Key{101}, Key{2});
  auto unique = iterTraits(keys.iterFifo()).unique<HashOnly, ModuloEqual>();
  ASS(unique.hasNext());
  ASS_EQ(unique.next().value, 1);
  ASS(unique.hasNext());
  ASS_EQ(unique.next().value, 2);
  ASS(!unique.hasNext());
}

TEST_FUN(perfectSharesEqualValues)
{
  Perfect<std::string> first(std::string("map-equality"));
  Perfect<std::string> equal(std::string("map-equality"));
  Perfect<std::string> different(std::string("other-map-value"));
  ASS(&*first == &*equal);
  ASS(first == equal);
  ASS(first != different);
}

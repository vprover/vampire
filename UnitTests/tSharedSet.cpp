/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#include "Lib/SharedSet.hpp"
#include "Test/UnitTesting.hpp"

#include <algorithm>
#include <array>
#include <iterator>
#include <limits>
#include <set>
#include <vector>

using namespace Lib;

namespace {

using Shared = SharedSet<int>;
using Model = std::set<int>;

const Shared* fromModel(const Model& model)
{
  std::vector<int> values(model.begin(), model.end());
  return Shared::getFromArray(values.data(), values.size());
}

void assertContents(const Shared* actual, const Model& expected)
{
  ASS_EQ(actual->size(), expected.size());
  ASS_EQ(actual->isEmpty(), expected.empty());
  auto iterator = actual->iter();
  unsigned index = 0;
  for (int value : expected) {
    ASS(iterator.hasNext());
    ASS_EQ(iterator.next(), value);
    ASS_EQ((*actual)[index++], value);
    ASS(actual->member(value));
  }
  ASS(!iterator.hasNext());
  ASS_EQ(actual, fromModel(expected));
  if (!expected.empty()) {
    ASS_EQ(actual->maxval(), *expected.rbegin());
  }
  if (expected.size() == 1) {
    ASS_EQ(actual->sval(), *expected.begin());
  }
}

}

TEST_FUN(all_small_subset_pairs)
{
  constexpr std::array<int, 5> domain{-3, -1, 0, 2, 5};
  std::array<Model, 32> models;
  std::array<const Shared*, 32> sets;
  for (unsigned mask = 0; mask < models.size(); ++mask) {
    for (unsigned bit = 0; bit < domain.size(); ++bit) {
      if (mask & (1U << bit)) {
        models[mask].insert(domain[bit]);
      }
    }
    sets[mask] = fromModel(models[mask]);
    assertContents(sets[mask], models[mask]);
    for (int candidate = -4; candidate <= 6; ++candidate) {
      ASS_EQ(sets[mask]->member(candidate), models[mask].count(candidate) != 0);
    }
  }

  for (unsigned i = 0; i < sets.size(); ++i) {
    for (unsigned j = 0; j < sets.size(); ++j) {
      const auto& left = models[i];
      const auto& right = models[j];
      Model united, intersected, difference;
      std::set_union(left.begin(), left.end(), right.begin(), right.end(),
                     std::inserter(united, united.end()));
      std::set_intersection(left.begin(), left.end(), right.begin(), right.end(),
                            std::inserter(intersected, intersected.end()));
      std::set_difference(left.begin(), left.end(), right.begin(), right.end(),
                          std::inserter(difference, difference.end()));
      assertContents(sets[i]->getUnion(sets[j]), united);
      assertContents(sets[i]->getIntersection(sets[j]), intersected);
      assertContents(sets[i]->subtract(sets[j]), difference);
      ASS_EQ(sets[i]->hasIntersection(sets[j]), !intersected.empty());
      ASS_EQ(sets[i]->isSubsetOf(sets[j]),
             std::includes(right.begin(), right.end(), left.begin(), left.end()));
      // Operations must preserve both immutable operands and canonical identity.
      assertContents(sets[i], left);
      assertContents(sets[j], right);
    }
  }
}

TEST_FUN(permutations_duplicates_and_input_immutability)
{
  std::array<int, 5> values{-3, -1, 0, 2, 5};
  const auto canonical = Shared::getFromArray(values.data(), values.size());
  unsigned permutations = 0;
  do {
    const auto before = values;
    ASS_EQ(Shared::getFromArray(values.data(), values.size()), canonical);
    ASS(values == before);
    std::vector<int> duplicated;
    for (int value : values) {
      duplicated.push_back(value);
      duplicated.push_back(value);
    }
    duplicated.push_back(values[0]);
    const auto duplicatedBefore = duplicated;
    ASS_EQ(Shared::getFromArray(duplicated.data(), duplicated.size()), canonical);
    ASS(duplicated == duplicatedBefore);
    ++permutations;
  } while (std::next_permutation(values.begin(), values.end()));
  ASS_EQ(permutations, 120);
}

TEST_FUN(ranges_and_iterator_construction)
{
  for (int first = -4; first <= 4; ++first) {
    for (int afterLast = first; afterLast <= 5; ++afterLast) {
      Model expected;
      Stack<int> reverseWithDuplicates;
      for (int value = first; value < afterLast; ++value) {
        expected.insert(value);
        reverseWithDuplicates.push(value);
        reverseWithDuplicates.push(value);
      }
      const auto range = Shared::getRange(first, afterLast);
      assertContents(range, expected);
      const auto fromIterator = Shared::getFromIterator(
          Stack<int>::Iterator(reverseWithDuplicates));
      ASS_EQ(range, fromIterator);
      ASS_EQ(range->getUnion(Shared::getEmpty()), range);
      ASS_EQ(range->subtract(range), Shared::getEmpty());
    }
  }
}

TEST_FUN(extreme_membership_and_singletons)
{
  const int minimum = std::numeric_limits<int>::min();
  const int maximum = std::numeric_limits<int>::max();
  Model expected{minimum, -1, 0, 1, maximum};
  const auto set = fromModel(expected);
  assertContents(set, expected);
  ASS(!set->member(minimum + 1));
  ASS(!set->member(maximum - 1));
  for (int value : expected) {
    const auto singleton = Shared::getSingleton(value);
    assertContents(singleton, Model{value});
    ASS(singleton->isSubsetOf(set));
    ASS_EQ(singleton->getIntersection(set), singleton);
    ASS_EQ(singleton->getUnion(set), set);
  }
}

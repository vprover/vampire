/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#include "Lib/IntUnionFind.hpp"
#include "Test/UnitTesting.hpp"

#include <algorithm>
#include <set>
#include <utility>
#include <vector>

using namespace Lib;

namespace {

using Component = std::set<int>;
using Partition = std::set<Component>;

// An undirected graph supplies an independent connectivity model. It has no
// parent pointers, representative selection or path compression.
class GraphModel {
public:
  explicit GraphModel(int size) : _edges(size, std::vector<bool>(size, false)) {}

  void connect(int left, int right)
  {
    _edges[left][right] = _edges[right][left] = true;
  }

  Component reachable(int start) const
  {
    Component seen{start};
    std::vector<int> pending{start};
    while (!pending.empty()) {
      int vertex = pending.back();
      pending.pop_back();
      for (int other = 0; other < size(); ++other) {
        if (_edges[vertex][other] && seen.insert(other).second) {
          pending.push_back(other);
        }
      }
    }
    return seen;
  }

  Partition partition() const
  {
    Partition result;
    for (int vertex = 0; vertex < size(); ++vertex) {
      result.insert(reachable(vertex));
    }
    return result;
  }

  int size() const { return _edges.size(); }

private:
  std::vector<std::vector<bool>> _edges;
};

Partition collect(IntUnionFind::ComponentIterator iterator, int size)
{
  Partition result;
  Component seen;
  while (iterator.hasNext()) {
    Component component;
    auto elements = iterator.next();
    while (elements.hasNext()) {
      int element = elements.next();
      ASS_GE(element, 0);
      ASS_L(element, size);
      ALWAYS(component.insert(element).second);
      ALWAYS(seen.insert(element).second);
    }
    ASS(!component.empty());
    ALWAYS(result.insert(component).second);
  }
  ASS_EQ(seen.size(), static_cast<unsigned>(size));
  return result;
}

void assertMatches(IntUnionFind& actual, const GraphModel& model)
{
  const IntUnionFind& constActual = actual;
  for (int vertex = 0; vertex < model.size(); ++vertex) {
    const auto expected = model.reachable(vertex);
    ASS_EQ(constActual.root(vertex), *expected.begin());
    for (int other = 0; other < model.size(); ++other) {
      ASS_EQ(constActual.root(vertex) == constActual.root(other),
             expected.count(other) != 0);
    }
  }
  const auto expected = model.partition();
  actual.evalComponents();
  ASS_EQ(actual.getComponentCount(), static_cast<int>(expected.size()));
  ASS(collect(IntUnionFind::ComponentIterator(actual), model.size()) == expected);
  // A second evaluation must preserve the cached partition.
  actual.evalComponents();
  ASS(collect(IntUnionFind::ComponentIterator(actual), model.size()) == expected);
}

void connectAndCheck(IntUnionFind& actual, GraphModel& model, int left, int right)
{
  bool changesPartition = model.reachable(left).count(right) == 0;
  ASS_EQ(actual.doUnion(left, right), changesPartition);
  model.connect(left, right);
  assertMatches(actual, model);
  NEVER(actual.doUnion(right, left));
  assertMatches(actual, model);
}

}

TEST_FUN(all_five_vertex_graphs_in_both_edge_orders)
{
  std::vector<std::pair<int, int>> edges;
  for (int left = 0; left < 5; ++left) {
    for (int right = 0; right < left; ++right) {
      edges.emplace_back(left, right);
    }
  }
  ASS_EQ(edges.size(), 10);
  for (unsigned mask = 0; mask < (1U << edges.size()); ++mask) {
    for (bool reverse : {false, true}) {
      IntUnionFind actual(5);
      GraphModel model(5);
      assertMatches(actual, model);
      for (unsigned index = 0; index < edges.size(); ++index) {
        unsigned bit = reverse ? edges.size() - index - 1 : index;
        if (mask & (1U << bit)) {
          connectAndCheck(actual, model, edges[bit].first, edges[bit].second);
        }
      }
    }
  }
}

TEST_FUN(reset_after_deep_chain_and_reuse)
{
  constexpr int size = 128;
  IntUnionFind actual(size);
  for (int vertex = size - 1; vertex > 0; --vertex) {
    ALWAYS(actual.doUnion(vertex, vertex - 1));
  }
  // Descending unions create a long chain before any root lookup compresses it.
  const IntUnionFind& constActual = actual;
  ASS_EQ(constActual.root(size - 1), 0);
  ASS_EQ(constActual.root(size - 1), 0);
  actual.evalComponents();
  ASS_EQ(actual.getComponentCount(), 1);
  actual.reset();
  GraphModel model(size);
  assertMatches(actual, model);
  for (int vertex = 0; vertex < size; vertex += 2) {
    ALWAYS(actual.doUnion(vertex, vertex + 1));
    model.connect(vertex, vertex + 1);
  }
  assertMatches(actual, model);
  actual.reset();
  actual.reset();
  assertMatches(actual, GraphModel(size));
}

TEST_FUN(component_iterator_snapshot_survives_union)
{
  IntUnionFind actual(6);
  GraphModel model(6);
  connectAndCheck(actual, model, 4, 1);
  connectAndCheck(actual, model, 5, 2);
  actual.evalComponents();
  auto snapshot = IntUnionFind::ComponentIterator(actual);
  const auto before = model.partition();
  ALWAYS(actual.doUnion(4, 5));
  model.connect(4, 5);
  ASS_EQ(actual.root(5), 1);
  // doUnion changes parents, but the documented snapshot stays valid until
  // evalComponents rebuilds its separate component lists.
  ASS(collect(snapshot, model.size()) == before);
  assertMatches(actual, model);
}

TEST_FUN(singleton_self_union_and_cached_partition)
{
  IntUnionFind actual(1);
  GraphModel model(1);
  assertMatches(actual, model);
  NEVER(actual.doUnion(0, 0));
  assertMatches(actual, model);
  actual.reset();
  assertMatches(actual, model);
}

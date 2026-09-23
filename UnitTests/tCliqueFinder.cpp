/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Lib/DHMap.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/Stack.hpp"

#include "FMB/CliqueFinder.hpp"

#include "Test/UnitTesting.hpp"

using namespace Lib;
using namespace FMB;

/**
 * The graphs CliqueFinder is asked about are the "these constants are pairwise different"
 * graphs FMB collects from ground unit disequalities, so they are given as a symmetric
 * neighbour map. Build one from a list of edges.
 */
class Graph {
public:
  void edge(unsigned a, unsigned b)
  {
    halfEdge(a,b);
    halfEdge(b,a);
  }

  unsigned maxCliqueSize() { return CliqueFinder::findMaxCliqueSize(&_map); }

  ~Graph()
  {
    DHMap<unsigned,DHSet<unsigned, FnvHash, IdentityHash>*, FnvHash, IdentityHash>::Iterator it(_map);
    while (it.hasNext()) {
      delete it.next();
    }
  }

private:
  void halfEdge(unsigned a, unsigned b)
  {
    DHSet<unsigned, FnvHash, IdentityHash>* nbs;
    if (!_map.find(a,nbs)) {
      nbs = new DHSet<unsigned, FnvHash, IdentityHash>();
      _map.insert(a,nbs);
    }
    nbs->insert(b);
  }

  DHMap<unsigned,DHSet<unsigned, FnvHash, IdentityHash>*, FnvHash, IdentityHash> _map;
};

// a single edge: the smallest interesting case, and the one FMB meets for a pair of
// distinct constants -- $$true != $$false in particular
TEST_FUN(single_edge)
{
  Graph g;
  g.edge(0,1);
  ASS_EQ(g.maxCliqueSize(),2);
}

// 0 - 1 - 2: two edges, but no triangle
TEST_FUN(path)
{
  Graph g;
  g.edge(0,1);
  g.edge(1,2);
  ASS_EQ(g.maxCliqueSize(),2);
}

// a centre with three leaves: the centre has three neighbours, none of them each other's
TEST_FUN(star)
{
  Graph g;
  g.edge(0,1);
  g.edge(0,2);
  g.edge(0,3);
  ASS_EQ(g.maxCliqueSize(),2);
}

TEST_FUN(triangle)
{
  Graph g;
  g.edge(0,1);
  g.edge(0,2);
  g.edge(1,2);
  ASS_EQ(g.maxCliqueSize(),3);
}

// the triangle must win over the disjoint edge
TEST_FUN(triangle_and_edge)
{
  Graph g;
  g.edge(0,1);
  g.edge(0,2);
  g.edge(1,2);
  g.edge(3,4);
  ASS_EQ(g.maxCliqueSize(),3);
}

// two disjoint edges: no clique bigger than an edge
TEST_FUN(two_disjoint_edges)
{
  Graph g;
  g.edge(0,1);
  g.edge(2,3);
  ASS_EQ(g.maxCliqueSize(),2);
}

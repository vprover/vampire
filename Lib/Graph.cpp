
/*
 * File Graph.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file Graph.cpp
 * Implements classes IntDiGraph, IntGraph.
 */

#include "Graph.hpp"

namespace Lib
{

unsigned IntDiGraph::addNode()
{
  CALL("IntDiGraph::addNode");

  unsigned res=_nodeCnt++;
  _neighs.expand(_nodeCnt);
  return res;
}

void IntDiGraph::addEdge(unsigned src, unsigned dest)
{
  CALL("IntDiGraph::addEgde");
  ASS_L(src, _nodeCnt);
  ASS_L(dest, _nodeCnt);

  _neighs[src].push(dest);
  _edges.insert(make_pair(src, dest));
}

unsigned IntDiGraph::edge(unsigned src, unsigned dest)
{
  CALL("IntDiGraph::egde");
  ASS_L(src, _nodeCnt);
  ASS_L(dest, _nodeCnt);

  return _edges.multiplicity(make_pair(src, dest));
}

void IntDiGraph::neighbours(unsigned node, unsigned*& neighArrPtr, unsigned& neighCnt)
{
  CALL("IntDiGraph::neighbours");
  ASS_L(node, _nodeCnt);

  neighCnt=_neighs[node].size();
  neighArrPtr=_neighs[node].begin();
}


IntSubgraph* IntSubgraph::getEmpty()
{
  static IntSubgraph empty;
  return &empty;
}


}


/*
 * File Graph.hpp.
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
 * @file Graph.hpp
 * Defines class IntDiGraph, IntGraph.
 *
 * Currently not used anywhere and not debugged!
 */


#ifndef __IntGraph__
#define __IntGraph__

#include <utility>

#include "DArray.hpp"
#include "DHMultiset.hpp"
#include "Numbering.hpp"
#include "Stack.hpp"

namespace Lib {

using namespace std;

/**
 * Class of directed multi-graph objects, whose nodes are
 * consecutive integers starting from zero.
 */
class IntDiGraph
{
public:
  IntDiGraph() : _nodeCnt(0) {}
  unsigned addNode();
  void addEdge(unsigned src, unsigned dest);

  /** Return degree of the edge from @b src to @b dest.
   * Return 0 it there is none. */
  unsigned edge(unsigned src, unsigned dest);

  /**
   * Assign an array of node's neighbours into neighArrPtr.
   * The array is guaranteed to be valid until a new edge
   * coming from the node @b node is added, new node is added,
   * or the graph is destroyed.
   */
  void neighbours(unsigned node, unsigned*& neighArrPtr, unsigned& neighCnt);

  unsigned size() const { return _nodeCnt; }

private:
  unsigned _nodeCnt;
  DArray<Stack<unsigned> > _neighs;
  DHMultiset<pair<unsigned,unsigned> > _edges;
};

/**
 * Class of multi-graph objects, whose nodes are
 * consecutive integers starting from zero.
 */
class IntGraph : IntDiGraph
{
public:
  unsigned addNode()
  {
    return IntDiGraph::addNode();
  }
  void addEgde(unsigned src, unsigned dest)
  {
    IntDiGraph::addEdge(src, dest);
    if(src!=dest) {
      IntDiGraph::addEdge(dest, src);
    }
  }
  unsigned edge(unsigned src, unsigned dest)
  {
    ASS_EQ(IntDiGraph::edge(src, dest), IntDiGraph::edge(dest, src));
    return IntDiGraph::edge(src, dest);
  }
  void neighbours(unsigned node, unsigned*& neighArrPtr, unsigned& neighCnt)
  {
    IntDiGraph::neighbours(node, neighArrPtr, neighCnt);
  }
};

class IntSubgraph
{
public:
  static IntSubgraph* getFull() { return 0; }
  static IntSubgraph* getEmpty();
private:
  DHMultiset<unsigned> _nodes;
};

template<typename T, class IGClass=IntGraph>
class Graph
{
public:
  void addNode(T obj)
  {
    unsigned inode=_ig.addNode();
    _num.assign(obj, inode);
  }
  void addEgde(T src, T dest)
  {
    _ig.addEdge( _num.get(src), _num.get(dest) );
  }
  unsigned edge(unsigned src, unsigned dest)
  {
    return _ig.edge( _num.get(src), _num.get(dest) );
  }
  bool contains(T obj)
  {
    return _num.contains(obj);
  }
private:
  Numbering<T> _num;
  IGClass _ig;
};

};

#endif /* __IntGraph__ */

/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file SCCAnalyzer.hpp
 * Defines a class SCCAnalyzer for analyzing strongly connected components.
 */

#ifndef __SCCAnalyzer__
#define __SCCAnalyzer__

#include "Forwards.hpp"

#include "DHMap.hpp"
#include "DHSet.hpp"
#include "Metaiterators.hpp"
#include "VirtualIterator.hpp"
#include "Stack.hpp"

namespace Lib {

template<typename T>
class MapToLIFOGraph
{
public:
  typedef MapToLIFO<T,T> Map;
  typedef T Node;
  typedef VirtualIterator<T> NodeIterator;

  MapToLIFOGraph(const Map& m) : _m(m)
  {
    CALL("MapToLIFOGraph::MapToLIFOGraph");

    typename Map::KeyIterator keys(_m);
    while(keys.hasNext()) {
      T n0 = keys.next();
      _nodes.push(n0);
      NodeIterator neighs = neighbors(n0);
      while(neighs.hasNext()) {
	_nodes.push(neighs.next());
      }
    }
    makeUnique(_nodes);
  }

  NodeIterator nodes() const
  {
    return pvi( typename Stack<T>::ConstIterator(_nodes) );
  }

  NodeIterator neighbors(T node) const
  {
    return pvi( _m.keyIterator(node) );
  }

  /**
   * Make sure all nodes in the iterator are present in the graph
   */
  template<class It>
  void ensureNodes(It nodeIt) {
    _nodes.loadFromIterator(nodeIt);
    makeUnique(_nodes);
  }

  size_t size() const { return _nodes.size(); }

private:
  Stack<T> _nodes;
  const Map& _m;
};

template<typename Graph>
class Subgraph
{
public:
  typedef typename Graph::Node Node;


  struct Filter
  {
    Filter(DHSet<Node>& forbidden) : _forbidden(forbidden) {}
    bool operator()(Node n) const { return !_forbidden.find(n); }
  private:
    DHSet<Node>& _forbidden;
  };

  typedef FilteredIterator<typename Graph::NodeIterator,Filter> NodeIterator;

  template<class It>
  Subgraph(Graph& gr, It forbiddenNodes)
   : _filter(_forbidden), _gr(gr)
  {
    CALL("Subgraph::Subgraph");

    _forbidden.loadFromIterator(forbiddenNodes);

    _size = 0;
    NodeIterator nit = nodes();
    while(nit.hasNext()) {
      nit.next();
      _size++;
    }
  }

  NodeIterator nodes() const
  {
    return NodeIterator(_gr.nodes(), _filter);
  }

  NodeIterator neighbors(Node node) const
  {
    return NodeIterator(_gr.neighbors(node), _filter);
  }

  size_t size() const { return _size; }

private:
  DHSet<Node> _forbidden;
  Filter _filter;
  const Graph& _gr;
  size_t _size;
};

/**
 *
 * Class Graph must contain:
 * - type Node
 * - type NodeIterator iterating over Node
 * - NodeIterator nodes()
 * - NodeIterator neighbors(Node node)
 */
template<class Graph>
class SCCAnalyzer {
public:
  typedef typename Graph::Node Node;
  typedef Stack<Node> NodeStack;

  SCCAnalyzer(const Graph& gr)
  {
    CALL("SCCAnalyzer::SCCAnalyzer");
    analyze(gr);
  }


  const NodeStack& breakingNodes() const { return _breakingNodes; }
  /**
   * Strong components are in topological order, so that
   * later ones can refer only to earlier ones.
   */
  const Stack<NodeStack>& components() const { return _components; }
private:

  typedef typename Graph::NodeIterator NodeIterator;

  //the names of the following variables come from the description of the
  //Gabow's algorithm on http://en.wikipedia.org/wiki/Cheriyan%E2%80%93Mehlhorn/Gabow_algorithm

  size_t C;
  DHMap<Node,size_t> nums;
  /** index of the strongly connected component node is in */
  DHMap<Node,size_t> scc;
  NodeStack S;
  NodeStack P;

  void analyze(const Graph& gr)
  {
    CALL("SCCAnalyzer::analyze");

    ASS_EQ(nums.size(),0);
    C = 0;
    NodeIterator nit = gr.nodes();
    while(nit.hasNext()) {
      Node v = nit.next();
      if(nums.find(v)) {
	continue;
      }
      traverse(v, gr);
    }
    makeUnique(_breakingNodes);
  }
  void traverse(Node v, const Graph& gr)
  {
    CALL("SCCAnalyzer::traverse");

    ALWAYS(nums.insert(v, C));
    C++;
    S.push(v);
    P.push(v);
    NodeIterator neigh = gr.neighbors(v);
    while(neigh.hasNext()) {
      Node w = neigh.next();
      size_t wNum;
      if(!nums.find(w,wNum)) {
	traverse(w, gr);
	continue;
      }
      if(scc.find(w)) { //edge (v,w) leads to a component discovered earlier
	continue;
      }
      //edge (v,w) creates a cycle
      _breakingNodes.push(w);
      while(nums.get(P.top())>wNum) {
	P.pop();
      }
    }
    if(v==P.top()) {
      size_t sccIndex = _components.size();
      //it should be a property of Gabow's algorithm that SCCs are
      //discovered in topological order.
      _components.push(Stack<Node>());
      NodeStack& compNodes = _components[sccIndex];
      Node cNode;
      do {
	cNode = S.pop();
	compNodes.push(cNode);
	scc.insert(cNode, sccIndex);
      } while(cNode!=v);
      P.pop();
    }
  }

  NodeStack _breakingNodes;
  Stack<NodeStack> _components;
};

}

#endif // __SCCAnalyzer__

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

  MapToLIFOGraph(Map& m) : _m(m)
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

  NodeIterator nodes()
  {
    return pvi( typename Stack<T>::Iterator(_nodes) );
  }

  NodeIterator neighbors(T node)
  {
    return pvi( _m.keyIterator(node) );
  }

  size_t size() const { return _nodes.size(); }

private:
  Stack<T> _nodes;
  Map& _m;
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

  NodeIterator nodes()
  {
    return NodeIterator(_gr.nodes(), _filter);
  }

  NodeIterator neighbors(Node node)
  {
    return NodeIterator(_gr.neighbors(node), _filter);
  }

  size_t size() const { return _size; }

private:
  DHSet<Node> _forbidden;
  Filter _filter;
  Graph& _gr;
  size_t _size;
};

/**
 *
 * Class Graph must contain:
 * - type Node
 * - type NodeIterator iterating over T
 * - NodeIterator nodes()
 * - NodeIterator neighbors(T node)
 */
template<class Graph>
class SCCAnalyzer {
public:
  typedef typename Graph::Node Node;
  typedef Stack<Node> NodeStack;

  SCCAnalyzer(Graph& gr) : _gr(gr)
  {
    CALL("SCCAnalyzer::SCCAnalyzer");
    analyze();
  }


  NodeStack& breakingNodes() { return _breakingNodes; }
  Stack<NodeStack>& components() { return _components; }
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

  void analyze()
  {
    CALL("SCCAnalyzer::analyze");

    ASS_EQ(nums.size(),0);
    C = 0;
    NodeIterator nit = _gr.nodes();
    while(nit.hasNext()) {
      Node v = nit.next();
      if(nums.find(v)) {
	continue;
      }
      traverse(v);
    }
    makeUnique(_breakingNodes);
  }
  void traverse(Node v)
  {
    CALL("SCCAnalyzer::traverse");

    ALWAYS(nums.insert(v, C));
    C++;
    S.push(v);
    P.push(v);
    NodeIterator neigh = _gr.neighbors(v);
    while(neigh.hasNext()) {
      Node w = neigh.next();
      size_t wNum;
      if(!nums.find(w,wNum)) {
	traverse(w);
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
      _components.push(Stack<Node>());
      NodeStack compNodes = _components[sccIndex];
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
  Graph& _gr;
};

}

#endif // __SCCAnalyzer__

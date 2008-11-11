/**
 * @file SubstitutionTree.hpp
 * Defines class SubstitutionTree.
 *
 * @since 16/08/2008 flight Sydney-San Francisco
 */

#ifndef __SubstitutionTree__
#define __SubstitutionTree__

#include "../Lib/VirtualIterator.hpp"
#include "../Lib/Comparison.hpp"
#include "../Lib/Int.hpp"
#include "../Lib/Stack.hpp"
#include "../Lib/List.hpp"
#include "../Lib/SkipList.hpp"
#include "../Lib/BinaryHeap.hpp"

#include "../Kernel/Forwards.hpp"
#include "../Kernel/DoubleSubstitution.hpp"
#include "Index.hpp"


using namespace std;
using namespace Lib;
using namespace Kernel;

namespace Indexing {


/**
 * Class of substitution trees. In fact, contains an array of substitution
 * trees.
 * @since 16/08/2008 flight Sydney-San Francisco
 */
class SubstitutionTree
{
private:
public:
  SubstitutionTree(int nodes);
  ~SubstitutionTree();
  
  void insert(Literal* lit, Clause* cls)
  { insert(getRootNodeIndex(lit), lit->args(), cls); }
  void remove(Literal* lit, Clause* cls)
  { remove(getRootNodeIndex(lit), lit->args(), cls); }

  void insert(TermList* term, Clause* cls);
  void remove(TermList* term, Clause* cls);
  
#ifdef VDEBUG
  string toString() const;
  bool isEmpty() const;
#endif
  
private:
  
  inline 
  int getRootNodeIndex(Literal* t)
  { return (int)t->header(); }

  inline 
  int getRootNodeIndex(TermList* t)
  {
    if(t->isVar()) {
      ASS(!t->isSpecialVar());
      return _numberOfTopLevelNodes-1;
    } else {
      return (int)t->term()->functor();
    }
  }
  
  enum NodeAlgorithm 
  {
    UNSORTED_LIST=1,
    SKIP_LIST=2,
    SET=3
  };

  class Node {
  public:
    inline
    Node() { term.makeEmpty(); }
    inline
    Node(const TermList* ts) : term(*ts) {}
    virtual ~Node();
    /** True if a leaf node */
    virtual bool isLeaf() const = 0;
    virtual bool isEmpty() const = 0;
    /** 
     * Return number of elements held in the node. If this operation
     * isn't supported by the datastructure, return -1. 
     */
    virtual int size() const { return -1; }
    virtual NodeAlgorithm algorithm() const = 0;
    
    static void split(Node** pnode, TermList* where, int var);

    /** term at this node */
    TermList term;
  };


  typedef VirtualIterator<Node**> NodeIterator;
  
  class IntermediateNode
    	: public Node
  {
  public:
    /** Build a new intermediate node which will serve as the root*/
    inline
    IntermediateNode()
    {}
    
    /** Build a new intermediate node */
    inline
    IntermediateNode(const TermList* ts)
    	: Node(ts)
    {}

    inline
    bool isLeaf() const { return false; };
    
    virtual NodeIterator allChildren() = 0;
    virtual NodeIterator variableChildren() = 0;
    /**
     * Returns pointer to pointer to child node with top symbol
     * of @b t. This pointer to node can be changed.
     * 
     * If canCreate is true and such child node does
     * not exist, pointer to null pointer is returned, and it's
     * assumed, that pointer to newly created node with given
     * top symbol will be put there.
     * 
     * If canCreate is false, null pointer is returned.
     */
    virtual Node** childByTop(TermList* t, bool canCreate) = 0;
    /**
     * Removes child which points to node with top symbol of @b t.
     * This node has to still exist in time of the call to remove method.
     */
    virtual void remove(TermList* t) = 0;

    void loadChildren(NodeIterator children);
    
  }; // class SubstitutionTree::IntermediateNode
    
  class Leaf
  : public Node
  {
  public:
    /** Build a new leaf which will serve as the root */
    inline
    Leaf()
    {}
    /** Build a new leaf */
    inline
    Leaf(const TermList* ts)
      : Node(ts)
    {}

    inline
    bool isLeaf() const { return true; };
    virtual ClauseIterator allCaluses() = 0;
    virtual void insert(Clause* cls) = 0;
    virtual void remove(Clause* cls) = 0;
    void loadClauses(ClauseIterator children);
  };
   
  //These classes and methods are defined in SubstitutionTree_Nodes.cpp
  class IsPtrToVarNodePredicate;
  class UListIntermediateNode;
  class UListLeaf;
  class SListIntermediateNode;
  class SListLeaf;
  class SetLeaf;
  static Leaf* createLeaf();
  static Leaf* createLeaf(TermList* ts);
  static void ensureLeafEfficiency(Leaf** l);
  static IntermediateNode* createIntermediateNode();
  static IntermediateNode* createIntermediateNode(TermList* ts);
  static void ensureIntermediateNodeEfficiency(IntermediateNode** inode);

  class Binding {
  public:
    /** Number of the variable at this node */
    int var;
    /** term at this node */
    TermList* term;
    /** Create new binding */
    Binding(int v,TermList* t) : var(v), term(t) {}
    /** Create uninitialised binding */
    Binding() {}

    struct Comparator
    {
      inline
      static Comparison compare(Binding& b1, Binding& b2)
      {
    	return Int::compare(b2.var, b1.var);
      }
    };
  }; // class SubstitutionTree::Binding

  
  //Using BinaryHeap leads to about 30% faster insertion,
  //but it doesn't support backtracking, which is needed 
  //for iteration
  //typedef BinaryHeap<Binding,Binding::Comparator> BindingQueue;
  typedef SkipList<Binding,Binding::Comparator> BindingQueue;
  typedef Stack<Binding> BindingStack;
  typedef Stack<const TermList*> TermStack;

  void insert(int number,TermList* args,Clause* cls);
  void remove(int number,TermList* args,Clause* cls);
  void insert(Node** node,BindingQueue& binding,Clause* clause);
  void remove(Node** node,BindingQueue& binding,Clause* clause);
  static bool sameTop(const TermList* ss,const TermList* tt);

  /** Number of top-level nodes */
  int _numberOfTopLevelNodes;
  /** Number of the next variable */
  int _nextVar;
  /** Array of nodes */
  Node** _nodes;
  
public:
  class ResultIterator
  : public IteratorCore<SLQueryResult>
  {
  public:
    bool hasNext()
    {
      if(leafClauses.hasNext()) {
	return true;
      }
    }
    SLQueryResult next()
    {
      if(leafClauses.hasNext()) {
	return SLQueryResult(leafClauses.next(), &subst);
      }
      
    }
  private:
    typedef List<Binding> BindingList; 
    struct BacktrackData {
      BacktrackData() {}
      BacktrackData(DoubleSubstitution::BacktrackData dsbd, List<Binding>* bindings)
      : dsbd(dsbd), bindings(bindings) {}
      DoubleSubstitution::BacktrackData dsbd;
      BindingList* bindings;
    };
    ClauseIterator leafClauses;
    DoubleSubstitution subst;
    BindingQueue bQueue;
    Stack<NodeIterator> nodeIterators;
    Stack<BacktrackData> btrData;
  protected:
    ResultIterator() : leafClauses(ClauseIterator::getEmpty()),
    	subst(), nodeIterators(4), btrData(4)
    {
    }
    void init(SubstitutionTree* t, Literal* query)
    {
      Node* root=t->_nodes[t->getRootNodeIndex(query)];
    }
    void init(SubstitutionTree* t, TermList* query)
    {
      Node* root=t->_nodes[t->getRootNodeIndex(query)];
    }
    bool enter(Node* n)
    {
      Binding bind=bQueue.pop();
      TermList qt;
      subst.apply(bind.term, 0, qt);
      
      TermList nt;
      subst.apply(&n->term, 1, nt);
      
      DoubleSubstitution assResult;
      BindingList* bindings(0);
      associate(qt, nt, bindings, assResult);
      
      DoubleSubstitution::BacktrackData dsbd = subst.backtrackableJoin(assResult);
      BindingList::Iterator blit(bindings);
      while(blit.hasNext()) {
	bQueue.insert(blit.next());
      }

      btrData.push(BacktrackData(dsbd, bindings));
      
      if(n->isLeaf()) {
	leafClauses=static_cast<Leaf*>(n)->allCaluses();
      } else {
	NodeIterator nit=getNodeIterator(static_cast<IntermediateNode*>(n));
	nodeIterators.push(nit);
      }
    }
    void leave(Node* n)
    {
      
    }
    NodeIterator getNodeIterator(IntermediateNode* n)
    {
      
    }
    virtual void associate(TermList qt, TermList nt, BindingList*& bindings, 
	    DoubleSubstitution& substitution)
    {
      
    }
  };

}; // class SubstiutionTree

} // namespace Indexing

#endif

/**
 * @file SubstitutionTree.hpp
 * Defines class SubstitutionTree.
 *
 * @since 16/08/2008 flight Sydney-San Francisco
 */

#ifndef __SubstitutionTree__
#define __SubstitutionTree__

#include "../Lib/VirtualIterator.hpp"
#include "../Lib/Stack.hpp"
#include "../Lib/Comparison.hpp"
#include "../Lib/BinaryHeap.hpp"
#include "../Lib/Int.hpp"

#include "../Lib/Map.hpp"
#include "../Lib/List.hpp"
#include "../Lib/SkipList.hpp"
#include "../Lib/DHMultiset.hpp"

#include "Index.hpp"

namespace Kernel {
  class TermList;
  class Clause;
};

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
  { insert(lit->header(), lit->args(), cls); }
  void remove(Literal* lit, Clause* cls)
  { remove(lit->header(), lit->args(), cls); }

  void insert(TermList* term, Clause* cls);
  void remove(TermList* term, Clause* cls);
  
  void insert(int number,TermList* args,Clause* cls);
  void remove(int number,TermList* args,Clause* cls);

#ifdef VDEBUG
  string toString() const;
  bool isEmpty() const;
#endif
  
private:
  
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

  class IsPtrToVarNodePredicate
  {
  public:
    static bool eval(Node** n)
    {
	return (*n)->term.isVar();
    }
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
    
    	
  template<typename T>
  class AccList
  : public List<T>
  {
  public:
    inline
    AccList(T head, AccList* tail): List<T>(head,tail) {}
    inline
    T* headPtr() { return &this->_head; }
    class PtrIterator 
    	: public IteratorCore<T*>
    {
    public:
      inline
      PtrIterator(AccList* lst) : _l(lst) {}
      inline
      bool hasNext() { return _l; }
      inline
      T* next() 
      {
	T* res=_l->headPtr(); 
	_l=static_cast<AccList*>(_l->tail()); 
	return res;
      }
    protected:
      AccList* _l;
    };
  };
    	
  class UListIntermediateNode
  : public IntermediateNode
  {
  public:
    inline
    UListIntermediateNode() : _nodes(0), _size(0) {}
    inline
    UListIntermediateNode(const TermList* ts) : IntermediateNode(ts), _nodes(0), _size(0) {}
    inline
    ~UListIntermediateNode()
    {
      if(_nodes) {
	_nodes->destroy();
      }
    }

    inline
    NodeAlgorithm algorithm() const { return UNSORTED_LIST; }
    inline
    bool isEmpty() const { return !_nodes; }
    inline
    int size() const { return _size; }
    inline
    NodeIterator allChildren() 
    {
      return NodeIterator(new NodeList::PtrIterator(_nodes));
    }
    inline
    NodeIterator variableChildren()
    {
      return NodeIterator(
	      new FilteredIterator<Node**,NodeList::PtrIterator,IsPtrToVarNodePredicate>(
		      NodeList::PtrIterator(_nodes)));
    }
    Node** childByTop(TermList* t, bool canCreate);
    void remove(TermList* t);
    
  private:
    typedef AccList<Node*> NodeList;
    NodeList* _nodes;
    int _size;
  };

  class UListLeaf
  : public Leaf
  {
  public:
    inline
    UListLeaf() : _clauses(0), _size(0) {}
    inline
    UListLeaf(const TermList* ts) : Leaf(ts), _clauses(0), _size(0) {}
    inline
    ~UListLeaf()
    {
      if(_clauses) {
	_clauses->destroy();
      }
    }

    inline
    NodeAlgorithm algorithm() const { return UNSORTED_LIST; }
    inline
    bool isEmpty() const { return !_clauses; }
    inline
    int size() const { return _size; }
    inline
    ClauseIterator allCaluses()
    {
      return ClauseIterator(new ProxyIterator<Clause*,ClauseList::Iterator>(
	      ClauseList::Iterator(_clauses)));
    }
    inline
    void insert(Clause* cls) 
    {
      _clauses=new ClauseList(cls, _clauses);
      _size++;
    }
    inline
    void remove(Clause* cls)
    {
      _clauses=_clauses->remove(cls);
      _size--;
    }
  private:
    typedef List<Clause*> ClauseList;
    ClauseList* _clauses;
    int _size;
  };

  
  class SListIntermediateNode
  : public IntermediateNode
  {
  public:
    SListIntermediateNode() {}
    SListIntermediateNode(const TermList* ts) : IntermediateNode(ts) {}
    
    static SListIntermediateNode* assimilate(IntermediateNode* orig); 

    inline
    NodeAlgorithm algorithm() const { return SKIP_LIST; }
    inline
    bool isEmpty() const { return _nodes.isEmpty(); }
#ifdef VDEBUG
    int size() const { return _nodes.size(); }
#endif
    inline
    NodeIterator allChildren() 
    {
      return NodeIterator(new ProxyIterator<Node**,NodeSkipList::PtrIterator> (
	      NodeSkipList::PtrIterator(_nodes)));
    }
    inline
    NodeIterator variableChildren()
    {
      return NodeIterator(
	      new WhileLimitedIterator<Node**,NodeSkipList::PtrIterator,IsPtrToVarNodePredicate> (
	      NodeSkipList::PtrIterator(_nodes)));
    }
    Node** childByTop(TermList* t, bool canCreate)
    {
      Node** res;
      bool found=_nodes.getPosition(t,res,canCreate);
      if(!found) {
	if(canCreate) {
	  *res=0;
	} else {
	  res=0;
	}
      }
      return res;
    }
    inline
    void remove(TermList* t)
    {
      _nodes.remove(t);
    }
    
  private:
    class NodePtrComparator
    {
    public:
      static Comparison compare(TermList* ts1,TermList* ts2)
      {
	if(ts1->isVar()) {
	  if(ts2->isVar()) {
	    return Int::compare(ts1->var(), ts2->var());
	  }
	  return LESS;
	}
	if(ts2->isVar()) {
	  return GREATER;
	}
	return Int::compare(ts1->term()->functor(), ts2->term()->functor());
      }
      inline
      static Comparison compare(Node* n1, Node* n2)
      {
	return compare(&n1->term, &n2->term);
      }
      inline
      static Comparison compare(TermList* ts1, Node* n2)
      {
	return compare(ts1, &n2->term);
      }
    };
    typedef SkipList<Node*,NodePtrComparator> NodeSkipList;
    NodeSkipList _nodes;
  };
  
  
  class SListLeaf
  : public Leaf
  {
  public:
    SListLeaf() {}
    SListLeaf(const TermList* ts) : Leaf(ts) {}
    
    static SListLeaf* assimilate(Leaf* orig); 

    inline
    NodeAlgorithm algorithm() const { return SKIP_LIST; }
    inline
    bool isEmpty() const { return _clauses.isEmpty(); }
#ifdef VDEBUG
    inline
    int size() const { return _clauses.size(); }
#endif
    inline
    ClauseIterator allCaluses()
    {
      return ClauseIterator(new ProxyIterator<Clause*,ClauseSkipList::Iterator>(
	      ClauseSkipList::Iterator(_clauses)));
    }
    void insert(Clause* cls) { _clauses.insert(cls); }
    void remove(Clause* cls) { _clauses.remove(cls); }
  private:
    class ClausePtrComparator
    {
    public:
      inline
      static Comparison compare(Clause* cls1, Clause* cls2)
      {
	return cls1 < cls2 ? LESS : cls1 == cls2 ? EQUAL : GREATER;
      }
    };
    typedef SkipList<Clause*,ClausePtrComparator> ClauseSkipList;
    ClauseSkipList _clauses;
    
    friend class SubstitutionTree;
  };

  class SetLeaf
  : public Leaf
  {
  public:
    SetLeaf() {}
    SetLeaf(const TermList* ts) : Leaf(ts) {}
    
    static SetLeaf* assimilate(Leaf* orig); 

    inline
    NodeAlgorithm algorithm() const { return SET; }
    inline
    bool isEmpty() const { return _clauses.isEmpty(); }
    inline
    ClauseIterator allCaluses()
    {
      return ClauseIterator(new ProxyIterator<Clause*,ClauseMultiset::Iterator>(
	      ClauseMultiset::Iterator(_clauses)));
    }
    inline
    void insert(Clause* cls) { _clauses.insert(cls); }
    inline
    void remove(Clause* cls) { _clauses.remove(cls); }
  private:
    class PtrHash
    {
    public:
      inline
      static unsigned hash(void* p)
      {
	return (unsigned)(reinterpret_cast<size_t>(p)>>2);
      }
    };
    typedef DHMultiset<Clause*,PtrHash> ClauseMultiset;
    ClauseMultiset _clauses;
    
  };
  
  
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
    class Comparator
    {
    public:
      inline
      static Comparison compare(Binding& b1, Binding& b2)
      {
	return Int::compare(b2.var, b1.var);
      }
    };
  }; // class SubstitutionTree::Binding

  typedef BinaryHeap<Binding,Binding::Comparator> BindingHeap;
  typedef Stack<Binding> BindingStack;
  typedef Stack<const TermList*> TermStack;

  inline
  static Leaf* createLeaf()
  {
    return new UListLeaf();
  }
  inline
  static Leaf* createLeaf(TermList* ts)
  {
    return new UListLeaf(ts);
  }
  static void ensureLeafEfficiency(Leaf** l);
  
  inline
  static IntermediateNode* createIntermediateNode()
  {
    return new UListIntermediateNode();
  }
  inline
  static IntermediateNode* createIntermediateNode(TermList* ts)
  {
    return new UListIntermediateNode(ts);
  }
  static void ensureIntermediateNodeEfficiency(IntermediateNode** inode);
  
  void insert(Node** node,BindingHeap& binding,Clause* clause);
  void remove(Node** node,BindingHeap& binding,Clause* clause);
  static bool sameTop(const TermList* ss,const TermList* tt);

  /** Number of top-level nodes */
  int _numberOfTopLevelNodes;
  /** Number of the next variable */
  int _nextVar;
  /** Array of nodes */
  Node** _nodes;
  
  /** Constants are stored here  */
  Map<int,List<Clause*>*,Hash> _constants;
}; // class SubstiutionTree

} // namespace Indexing

#endif

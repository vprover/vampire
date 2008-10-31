/**
 * @file SubstitutionTree.hpp
 * Defines class SubstitutionTree.
 *
 * @since 16/08/2008 flight Sydney-San Francisco
 */

#ifndef __SubstitutionTree__
#define __SubstitutionTree__

#include "../Lib/Stack.hpp"
#include "../Lib/Comparison.hpp"
#include "../Lib/BinaryHeap.hpp"
#include "../Lib/Int.hpp"

#include "../Lib/Map.hpp"
#include "../Lib/List.hpp"

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
  {
    insert(lit->header(), lit->args(), cls);
  }
  void remove(Literal* lit, Clause* cls)
  {
    remove(lit->header(), lit->args(), cls);
  }

  void insert(TermList* term, Clause* cls)
  {
    ASS(!term->isEmpty());
    if(term->isVar()) {
      ASS(!term->isSpecialVar());
      BindingHeap bh;
      insert(_nodes+_numberOfTopLevelNodes-1, bh, cls);
    } else {
      insert(term->term()->functor(), term->term()->args(), cls);
    }
  }
  void remove(TermList* term, Clause* cls)
  {
    ASS(!term->isEmpty());
    if(term->isVar()) {
      ASS(!term->isSpecialVar());
      BindingHeap bh;
      remove(_nodes+_numberOfTopLevelNodes-1, bh, cls);
    } else {
      remove(term->term()->functor(), term->term()->args(), cls);
    }
  }
  
  void insert(int number,TermList* args,Clause* cls);
  void remove(int number,TermList* args,Clause* cls);

#ifdef VDEBUG
  string toString() const;
  bool isEmpty() const;
#endif
  
private:
  class Node {
  public:
    Node() {}
    Node(TermList* ts) : term(*ts) {}
    virtual ~Node() {}
    /** True if a leaf node */
    virtual bool isLeaf() const = 0;
    virtual bool isEmpty() const = 0;
    
    static void split(Node** pnode, TermList* where, int var);

    /** term at this node */
    TermList term;
  };

  
  template<typename T>
    class Iterator;
  
  template<typename T>
  class IteratorCore {
  public:
    IteratorCore() : _refCnt(0) {}
    virtual ~IteratorCore() { ASS(_refCnt==0); }
    virtual bool hasNext() = 0;
    virtual T next() = 0;
  private:
    mutable int _refCnt;
    
    friend class SubstitutionTree::Iterator<T>;
  };
  
  template<typename T>
  class Iterator {
  public:
    Iterator() : _core(0) {}
    Iterator(IteratorCore<T>* core) : _core(core) { _core->_refCnt++;}
    Iterator(const Iterator& obj) : _core(obj._core) { _core->_refCnt++;}
    ~Iterator() 
    { 
      if(_core) {
	_core->_refCnt--; 
	if(!_core->_refCnt) {
	  delete _core;
	}
      }
    }
    Iterator& operator=(const Iterator& obj) 
    {
      IteratorCore<T>* oldCore=_core;
      _core=obj._core;
      if(_core) {
	_core->_refCnt++;
      }
      if(oldCore) {
	oldCore->_refCnt--;
	if(!oldCore->_refCnt) {
	  delete oldCore;
	}
      }
    }
    bool hasNext() { return _core->hasNext(); }
    T next() { return _core->next(); }
  private:
    IteratorCore<T>* _core;
  };
  
  typedef Iterator<Node**> NodeIterator;
  typedef Iterator<Clause*> ClauseIterator;
  
  template<typename T, class Inner>
  class ProxyIterator 
  	: public IteratorCore<T>
  {
    Inner inn;
  public:
    ProxyIterator(Inner inn) :inn(inn) {}
    virtual bool hasNext() { return inn.hasNext(); };
    virtual T next() { return inn.next(); }; 
  };

  class IntermediateNode
    	: public Node
  {
  public:
    /** Build a new intermediate node which will serve as the root*/
    IntermediateNode()
    {}
    
    /** Build a new intermediate node */
    IntermediateNode(TermList* ts)
    	: Node(ts)
    {}

    virtual bool isLeaf() const { return false; };
    
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
    Leaf()
    {}
    /** Build a new leaf */
    Leaf(TermList* ts)
      : Node(ts)
    {}

    virtual bool isLeaf() const { return true; };
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
    AccList(T head, AccList* tail): List<T>(head,tail) {}
    T* headPtr() { return &this->_head; }
    class PtrIterator 
    	: public SubstitutionTree::IteratorCore<T*>
    {
    public:
      PtrIterator(AccList* lst) : _l(lst) {}
      virtual bool hasNext() { return _l; }
      virtual T* next() 
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
    UListIntermediateNode() : _nodes(0) {}
    UListIntermediateNode(TermList* ts) : IntermediateNode(ts), _nodes(0) {}
    ~UListIntermediateNode()
    {
      if(_nodes) {
	_nodes->destroy();
      }
    }

    virtual bool isEmpty() const
    {
      return !_nodes;
    }
    virtual NodeIterator allChildren() 
    {
      return new NodeList::PtrIterator(_nodes);
    }
    virtual NodeIterator variableChildren()
    {
      return new VarIterator(_nodes);
    }
    virtual Node** childByTop(TermList* t, bool canCreate);
    virtual void remove(TermList* t);
    
  private:
    typedef AccList<Node*> NodeList;
    NodeList* _nodes;
    class VarIterator 
    	: public SubstitutionTree::AccList<Node*>::PtrIterator
    {
    public:
      VarIterator(NodeList* lst) : PtrIterator(lst) {}
      virtual bool hasNext() 
      {
	while(_l && !_l->head()->term.isVar()) {
	  _l=static_cast<NodeList*>(_l->tail());
	}
	return _l;
      }
    };
  };

  class UListLeaf
    	: public Leaf
  {
  public:
    UListLeaf() : _clauses(0) {}
    UListLeaf(TermList* ts) : Leaf(ts), _clauses(0) {}
    ~UListLeaf()
    {
      if(_clauses) {
	_clauses->destroy();
      }
    }

    bool isEmpty() const
    {
      return !_clauses;
    }
    virtual ClauseIterator allCaluses()
    {
      return new ProxyIterator<Clause*,ClauseList::Iterator>(
	      ClauseList::Iterator(_clauses));
    }
    virtual void insert(Clause* cls) 
    {
      _clauses=new ClauseList(cls, _clauses);
    }
    virtual void remove(Clause* cls)
    {
      _clauses=_clauses->remove(cls);
    }
  private:
    typedef List<Clause*> ClauseList;
    ClauseList* _clauses;
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
      static Comparison compare(Binding& b1, Binding& b2)
      {
	return Int::compare(b2.var, b1.var);
      }
    };
  }; // class SubstitutionTree::Binding

  typedef BinaryHeap<Binding,Binding::Comparator> BindingHeap;
  typedef Stack<Binding> BindingStack;
  typedef Stack<const TermList*> TermStack;

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

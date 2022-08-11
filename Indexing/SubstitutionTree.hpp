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
 * @file SubstitutionTree.hpp
 * Defines class SubstitutionTree.
 *
 * @since 16/08/2008 flight Sydney-San Francisco
 */

#ifndef __SubstitutionTree__
#define __SubstitutionTree__

#include <utility>

#include "Forwards.hpp"

#include "Lib/VirtualIterator.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Comparison.hpp"
#include "Lib/Int.hpp"
#include "Lib/Stack.hpp"
#include "Lib/List.hpp"
#include "Lib/SkipList.hpp"
#include "Lib/BinaryHeap.hpp"
#include "Lib/Backtrackable.hpp"
#include "Lib/ArrayMap.hpp"
#include "Lib/Array.hpp"
#include "Lib/BiMap.hpp"
#include "Kernel/ApplicativeHelper.hpp"

#include "Kernel/RobSubstitution.hpp"
#include "Kernel/Renaming.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/SortHelper.hpp"
#include "Shell/Options.hpp"
#include "Kernel/OperatorType.hpp"
#include "Kernel/Signature.hpp"

#include "Lib/Allocator.hpp"

#include "Index.hpp"

#if VDEBUG
#include <iostream>
#endif

using namespace std;
using namespace Lib;
using namespace Kernel;

#define UARR_INTERMEDIATE_NODE_MAX_SIZE 4

#define REORDERING 1

namespace Indexing {

/**
 * Class of substitution trees. In fact, contains an array of substitution
 * trees.
 * @since 16/08/2008 flight Sydney-San Francisco
 */
template<class LeafData_>
class SubstitutionTree
{

public:
  using LeafData = LeafData_;
  using TermQueryResultIterator = VirtualIterator<TermQueryResult<LeafData>>;

  CLASS_NAME(SubstitutionTree);
  USE_ALLOCATOR(SubstitutionTree);

  SubstitutionTree(int nodes);
  ~SubstitutionTree();

  friend std::ostream& operator<<(std::ostream& out, SubstitutionTree const& self)
  { return out << "SubstitutionTree(...)"; }
  
  typedef VirtualIterator<LeafData&> LDIterator;

  class LDComparator
  {
  public:
    template<class LD>
    static Comparison compare(const LD& ld1, const LD& ld2)
    {
      return ld1 < ld2 ? Comparison::LESS 
           : ld1 > ld2 ? Comparison::GREATER
           : Comparison::EQUAL;
    }

  };

  static bool isGround(Literal* literal) { return literal->ground(); }
  static bool isGround(TermList term) { return term.ground(); }

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
    Node(TermList ts) : term(ts) { }
    virtual ~Node();
    /** True if a leaf node */
    virtual bool isLeaf() const = 0;
    virtual bool isEmpty() const = 0;
    virtual bool withSorts(){ return false; }
    /**
     * Return number of elements held in the node.
     *
     * Descendant classes should override this method.
     */
    virtual int size() const = 0;
    virtual NodeAlgorithm algorithm() const = 0;

    /**
     * Remove all referenced structures without destroying them.
     *
     * This is used when the implementation of a node is being changed.
     * The current node will be deleted, but we don't want to destroy
     * structures, that are taken over by the new node implementation.
     */
    virtual void makeEmpty() { term.makeEmpty(); }
    static void split(Node** pnode, TermList* where, int var);

#if VDEBUG
    virtual void assertValid() const = 0;
#endif

    /** term at this node */
    TermList term;

    virtual void print(unsigned depth=0, std::ostream& out = std::cout) const = 0;
    void printDepth(unsigned depth) const 
    { while(depth-->0){ cout << " "; } }

    friend std::ostream& operator<<(std::ostream& out, Node const& self)
    { self.print(0, out); return out; }
  };


  typedef VirtualIterator<Node**> NodeIterator;
  typedef VirtualIterator<Node const *> ConstNodeIterator;

  class IntermediateNode
    	: public Node
  {
  public:
    /** Build a new intermediate node which will serve as the root*/
    inline
    IntermediateNode(unsigned childVar) : childVar(childVar) {}

    /** Build a new intermediate node */
    inline
    IntermediateNode(TermList ts, unsigned childVar) : Node(ts), childVar(childVar) {}

    inline
    bool isLeaf() const final override { return false; };

    virtual NodeIterator allChildren() = 0;
    virtual ConstNodeIterator allChildren() const = 0;
    virtual NodeIterator variableChildren() = 0;
    /**
     * Return pointer to pointer to child node with top symbol
     * of @b t. This pointer to node can be changed.
     *
     * If canCreate is true and such child node does
     * not exist, pointer to null pointer is returned, and it's
     * assumed, that pointer to newly created node with given
     * top symbol will be put there.
     *
     * If canCreate is false, null pointer is returned in case
     * suitable child does not exist.
     */
    virtual Node** childByTop(TermList t, bool canCreate) = 0;


    /**
     * Remove child which points to node with top symbol of @b t.
     * This node has to still exist in time of the call to remove method.
     */
    virtual void remove(TermList t) = 0;

    /**
     * Remove all children of the node without destroying them.
     */
    virtual void removeAllChildren() = 0;

    void destroyChildren();

    void makeEmpty() final override 
    {
      Node::makeEmpty();
      removeAllChildren();
    }

    void loadChildren(NodeIterator children);

    const unsigned childVar;

    virtual void print(unsigned depth=0, std::ostream& out = std::cout) const final override 
    {
       auto children = allChildren();
       Node::printDepth(depth);
       cout << "I [" << childVar << "] with " << Node::term.toString() << endl;
       while(children.hasNext()){
         children.next()->print(depth+1, out);
       }
    }

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
    Leaf(TermList ts) : Node(ts) {}

    inline
    bool isLeaf() const final override { return true; };
    virtual LDIterator allChildren() const = 0;
    virtual void insert(LeafData ld) = 0;
    virtual void remove(LeafData ld) = 0;
    void loadChildren(LDIterator children);

    virtual void print(unsigned depth=0, std::ostream& out = std::cout) const final override {
       auto children = allChildren();
       while(children.hasNext()){
         this->printDepth(depth);
         out << children.next() << endl;
       } 
    }
  };

  //These classes and methods are defined in SubstitutionTree_Nodes.cpp
  class UListLeaf;
  class SListIntermediateNode;
  class SListLeaf;
  class SetLeaf;
  static Leaf* createLeaf();
  static Leaf* createLeaf(TermList ts);
  static void ensureLeafEfficiency(Leaf** l);
  static IntermediateNode* createIntermediateNode(unsigned childVar);
  static IntermediateNode* createIntermediateNode(TermList ts, unsigned childVar);
  static void ensureIntermediateNodeEfficiency(IntermediateNode** inode);

  struct IsPtrToVarNodeFn
  {
    bool operator()(Node** n)
    {
      return (*n)->term.isVar();
    }
  };

  class UArrIntermediateNode
  : public IntermediateNode
  {
  public:
    inline
    UArrIntermediateNode(unsigned childVar) : IntermediateNode(childVar), _size(0)
    {
      _nodes[0]=0;
    }
    inline
    UArrIntermediateNode(TermList ts, unsigned childVar) : IntermediateNode(ts, childVar), _size(0)
    {
      _nodes[0]=0;
    }

    ~UArrIntermediateNode()
    {
      if(!isEmpty()) {
        this->destroyChildren();
      }
    }

    void removeAllChildren() final override 
    {
      _size=0;
      _nodes[0]=0;
    }

    NodeAlgorithm algorithm() const final override  { return UNSORTED_LIST; }
    bool isEmpty() const final override { return !_size; }
    int size() const final override  { return _size; }
    NodeIterator allChildren() final override
    { return pvi( PointerPtrIterator<Node*>(&_nodes[0],&_nodes[_size]) ); }
    ConstNodeIterator allChildren() const final override
    { return pvi( iterTraits(ConstPointerPtrIterator<Node*>(&_nodes[0],&_nodes[_size])).map([](Node* const* n) { return (Node const*) *n; }) ); }

    NodeIterator variableChildren() final override
    {
      return pvi( getFilteredIterator(PointerPtrIterator<Node*>(&_nodes[0],&_nodes[_size]),
  	    IsPtrToVarNodeFn()) );
    }
    virtual Node** childByTop(TermList t, bool canCreate) final override;
    void remove(TermList t) final override;

#if VDEBUG
    virtual void assertValid() const final override
    {
      ASS_ALLOC_TYPE(this,"SubstitutionTree::UArrIntermediateNode");
    }
#endif

    CLASS_NAME(SubstitutionTree::UArrIntermediateNode);
    USE_ALLOCATOR(UArrIntermediateNode);

    int _size;
    Node* _nodes[UARR_INTERMEDIATE_NODE_MAX_SIZE+1];
  };

  class SListIntermediateNode
  : public IntermediateNode
  {
  public:
    SListIntermediateNode(unsigned childVar) : IntermediateNode(childVar) {}
    SListIntermediateNode(TermList ts, unsigned childVar) : IntermediateNode(ts, childVar) {}

    ~SListIntermediateNode()
    {
      if(!isEmpty()) {
        this->destroyChildren();
      }
    }

    void removeAllChildren() final override 
    {
      while(!_nodes.isEmpty()) {
        _nodes.pop();
      }
    }

    static IntermediateNode* assimilate(IntermediateNode* orig);

    inline
    NodeAlgorithm algorithm() const final override  { return SKIP_LIST; }
    inline
    bool isEmpty() const final override { return _nodes.isEmpty(); }
    int size() const final override  { return _nodes.size(); }
#if VDEBUG
    virtual void assertValid() const final override
    {
      ASS_ALLOC_TYPE(this,"SubstitutionTree::SListIntermediateNode");
    }
#endif
    inline
    NodeIterator allChildren() final override
    { return pvi( typename NodeSkipList::PtrIterator(_nodes) ); }

    ConstNodeIterator allChildren() const final override
    { return pvi(iterTraits( typename NodeSkipList::Iterator(_nodes)).map([](Node* n) { return (Node const* ) n; } )); }

    inline
    NodeIterator variableChildren() final override
    {
      return pvi( getWhileLimitedIterator(
  		    typename NodeSkipList::PtrIterator(_nodes),
  		    IsPtrToVarNodeFn()) );
    }
    virtual Node** childByTop(TermList t, bool canCreate) final override
    {
      CALL("SubstitutionTree::SListIntermediateNode::childByTop");

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
    void remove(TermList t) final override
    {
      _nodes.remove(t);
    }

    CLASS_NAME(SubstitutionTree::SListIntermediateNode);
    USE_ALLOCATOR(SListIntermediateNode);

    class NodePtrComparator
    {
    public:
      static Comparison compare(TermList t1,TermList t2)
      {
        CALL("SubstitutionTree::SListIntermediateNode::NodePtrComparator::compare");

        if(t1.isVar()) {
          if(t2.isVar()) {
            return Int::compare(t1.var(), t2.var());
          }
          return LESS;
        }
        if(t2.isVar()) {
          return GREATER;
        }
        return Int::compare(t1.term()->functor(), t2.term()->functor());
      }

      static Comparison compare(Node* n1, Node* n2)
      { return compare(n1->term, n2->term); }
      static Comparison compare(TermList t1, Node* n2)
      { return compare(t1, n2->term); }
    };
    typedef SkipList<Node*,NodePtrComparator> NodeSkipList;
    NodeSkipList _nodes;
  };

  class Binding {
  public:
    /** Number of the variable at this node */
    unsigned var;
    /** term at this node */
    TermList term;
    /** Create new binding */
    Binding(int v,TermList t) : var(v), term(t) {}

    struct Comparator
    {
      inline
      static Comparison compare(Binding& b1, Binding& b2)
      {
    	return Int::compare(b2.var, b1.var);
      }
    };
    friend std::ostream& operator<<(std::ostream& out, Binding const& self)
    { return out << self.var << " -> " << self.term; }
  }; // class SubstitutionTree::Binding

  struct SpecVarComparator
  {
    inline
    static Comparison compare(unsigned v1, unsigned v2)
    { return Int::compare(v2, v1); }
    inline
    static unsigned max()
    { return 0u; }
  };

  typedef DHMap<unsigned,TermList,IdentityHash,Hash> BindingMap;
  //Using BinaryHeap as a BindingQueue leads to about 30% faster insertion,
  //that when SkipList is used.
  typedef BinaryHeap<Binding,typename Binding::Comparator> BindingQueue;
  //typedef SkipList<Binding,Binding::Comparator> BindingQueue;
//  typedef SkipList<unsigned,SpecVarComparator> SpecVarQueue;
  typedef BinaryHeap<unsigned,SpecVarComparator> SpecVarQueue;
  typedef Stack<unsigned> VarStack;

  void getBindings(Term* t, BindingMap& binding);

  Leaf* findLeaf(Node* root, BindingMap& svBindings);

  void insert(Node** node,BindingMap& binding,LeafData ld);
  void remove(Node** node,BindingMap& binding,LeafData ld);

  /** Number of the next variable */
  int _nextVar;
  /** Array of nodes */
  ZIArray<Node*> _nodes;

  class LeafIterator
  : public IteratorCore<Leaf*>
  {
  public:
    LeafIterator(SubstitutionTree* st)
    : _nextRootPtr(st->_nodes.begin()), _afterLastRootPtr(st->_nodes.end()),
    _nodeIterators(8) {}
    bool hasNext();
    Leaf* next()
    {
      ASS(_curr->isLeaf());
      return static_cast<Leaf*>(_curr);
    }
  private:
    Node** _nextRootPtr;
    Node** _afterLastRootPtr;
    Node* _curr;
    Stack<NodeIterator> _nodeIterators;
  };

  typedef pair<LeafData*, ResultSubstitutionSP> QueryResult;


  class GenMatcher;

  /**
   * Iterator, that yields generalizations of given term/literal.
   */
  class FastGeneralizationsIterator
  : public IteratorCore<QueryResult>
  {
  public:
    FastGeneralizationsIterator(SubstitutionTree* parent, Node* root, Term* query,
            bool retrieveSubstitution, bool reversed,bool withoutTop, MismatchHandler* hndler = 0);

    ~FastGeneralizationsIterator();

    QueryResult next();
    bool hasNext();
  protected:
    void createInitialBindings(Term* t);
    void createReversedInitialBindings(Term* t);

    bool findNextLeaf();
    bool enterNode(Node*& node);

    /** We should include substitutions in the results */
    bool _retrieveSubstitution;
    /** The iterator is currently in a leaf
     *
     * This is false in the beginning when it is in the root */
    bool _inLeaf;

    GenMatcher* _subst;

    LDIterator _ldIterator;

    Renaming _resultNormalizer;

    Node* _root;
    SubstitutionTree* _tree;

    Stack<void*> _alternatives;
    Stack<unsigned> _specVarNumbers;
    Stack<NodeAlgorithm> _nodeTypes;
  };

  class InstMatcher;

  /**
   * Iterator, that yields generalizations of given term/literal.
   */
  class FastInstancesIterator
  : public IteratorCore<QueryResult>
  {
  public:
    FastInstancesIterator(SubstitutionTree* parent, Node* root, Term* query,
	    bool retrieveSubstitution, bool reversed, bool withoutTop, 
      MismatchHandler* hndler = 0);
    ~FastInstancesIterator();

    bool hasNext();
    QueryResult next();
  protected:
    void createInitialBindings(Term* t);
    void createReversedInitialBindings(Term* t);
    bool findNextLeaf();

    bool enterNode(Node*& node);

  private:
    bool _retrieveSubstitution;
    bool _inLeaf;
    LDIterator _ldIterator;

    InstMatcher* _subst;

    Renaming _resultDenormalizer;
    Node* _root;

    Stack<void*> _alternatives;
    Stack<unsigned> _specVarNumbers;
    Stack<NodeAlgorithm> _nodeTypes;
#if VDEBUG
    SubstitutionTree* _tree;
#endif
  };

  class UnificationsIterator
  : public IteratorCore<QueryResult>
  {
  public:
    UnificationsIterator(SubstitutionTree* parent, Node* root, Term* query, 
      bool retrieveSubstitution, bool reversed, bool withoutTop,
      MismatchHandler* hndler = 0);
    ~UnificationsIterator();

    bool hasNext();
    QueryResult next();
  protected:
    virtual bool associate(TermList query, TermList node);
    virtual NodeIterator getNodeIterator(IntermediateNode* n);

    void createInitialBindings(Term* t);
    /**
     * For a binary comutative literal, creates initial bindings,
     * where the order of special variables is reversed.
     */
    void createReversedInitialBindings(Term* t);
    bool findNextLeaf();
    bool enter(Node* n, BacktrackData& bd);


    static const int QUERY_BANK=0;
    static const int RESULT_BANK=1;
    static const int NORM_QUERY_BANK=2;
    static const int NORM_RESULT_BANK=3;

    RobSubstitution subst;
    VarStack svStack;

  private:
    bool retrieveSubstitution;
    bool inLeaf;
    LDIterator ldIterator;
    Stack<NodeIterator> nodeIterators;
    Stack<BacktrackData> bdStack;
    bool clientBDRecording;
    BacktrackData clientBacktrackData;
    Renaming queryNormalizer;
    MismatchHandler* handler;
    UnificationConstraintStack constraints;
#if VDEBUG
    SubstitutionTree* tree;
#endif
  };
  friend class UnificationsIterator;

/*
  class GeneralizationsIterator
  : public UnificationsIterator
  {
  public:
    GeneralizationsIterator(SubstitutionTree* parent, Node* root, Term* query, bool retrieveSubstitution, bool reversed, bool withoutTop, bool useC)
    : UnificationsIterator(parent, root, query, retrieveSubstitution, reversed, withoutTop, useC) {}; 

  protected:
    virtual bool associate(TermList query, TermList node);
    virtual NodeIterator getNodeIterator(IntermediateNode* n);
  };
*/
/*
  class InstancesIterator
  : public UnificationsIterator
  {
  public:
    InstancesIterator(SubstitutionTree* parent, Node* root, Term* query, bool retrieveSubstitution, bool reversed,bool withoutTop,bool useC)
    : UnificationsIterator(parent, root, query, retrieveSubstitution, reversed, withoutTop,useC) {}; 
  protected:
    virtual bool associate(TermList query, TermList node);
    virtual NodeIterator getNodeIterator(IntermediateNode* n);
  };
*/

#if VDEBUG
public:
  static vstring nodeToString(Node* topNode);
  vstring toString() const;
  bool isEmpty() const;

  int _iteratorCnt;
#endif
}; // class SubstitutionTree


} // namespace Indexing


#include "Indexing/SubstitutionTree.cpp"
#include "Indexing/SubstitutionTree_Nodes.cpp"
#include "Indexing/SubstitutionTree_FastGen.cpp"
#include "Indexing/SubstitutionTree_FastInst.cpp"

#endif

/**
 * @file SubstitutionTree.hpp
 * Defines class SubstitutionTree.
 *
 * @since 16/08/2008 flight Sydney-San Francisco
 */

#ifndef __SubstitutionTree__
#define __SubstitutionTree__

#include <utility>

#include "../Forwards.hpp"

#include "../Lib/VirtualIterator.hpp"
#include "../Lib/Comparison.hpp"
#include "../Lib/Int.hpp"
#include "../Lib/Stack.hpp"
#include "../Lib/List.hpp"
#include "../Lib/SkipList.hpp"
#include "../Lib/BinaryHeap.hpp"
#include "../Lib/BacktrackData.hpp"
#include "../Lib/ArrayMap.hpp"

#include "../Kernel/DoubleSubstitution.hpp"
#include "../Kernel/MMSubstitution.hpp"
#include "../Kernel/Matcher.hpp"
#include "../Kernel/Renaming.hpp"
#include "../Kernel/Clause.hpp"

#include "Index.hpp"

#if VDEBUG

#include <iostream>
#include "../Test/Output.hpp"

#endif

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
public:
  SubstitutionTree(int nodes);
  ~SubstitutionTree();

protected:

  struct LeafData {
    LeafData() {}
    LeafData(Clause* cls, Literal* literal, TermList term)
    : clause(cls), literal(literal), term(term) {}
    LeafData(Clause* cls, Literal* literal)
    : clause(cls), literal(literal) { term.makeEmpty(); }
    inline
    bool operator==(const LeafData& o)
    { return clause==o.clause && literal==o.literal && term==o.term; }

    Clause* clause;
    Literal* literal;
    TermList term;
  };
  typedef VirtualIterator<LeafData&> LDIterator;

  class LDComparator
  {
  public:
    inline
    static Comparison compare(const LeafData& ld1, const LeafData& ld2)
    {
      return (ld1.clause<ld2.clause)? LESS :
      	(ld1.clause>ld2.clause)? GREATER :
      	(ld1.literal<ld2.literal)? LESS :
	(ld1.literal>ld2.literal)? GREATER :
    	(ld1.term<ld2.term)? LESS :
	(ld1.term>ld2.term)? GREATER : EQUAL;
    }
  };

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
    /**
     * Return number of elements held in the node. If this operation
     * isn't supported by the datastructure, return -1.
     */
    virtual int size() const { return -1; }
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

    /** term at this node */
    TermList term;
  };


  typedef VirtualIterator<Node**> NodeIterator;
  typedef List<Node*> NodeList;

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
    IntermediateNode(TermList ts) : Node(ts) {}

    inline
    bool isLeaf() const { return false; };

    virtual NodeIterator allChildren() = 0;
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
     * If canCreate is false, null pointer is returned.
     */
    virtual Node** childByTop(TermList t, bool canCreate) = 0;
    /**
     * Remove child which points to node with top symbol of @b t.
     * This node has to still exist in time of the call to remove method.
     */
    virtual void remove(TermList t) = 0;

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
    Leaf(TermList ts) : Node(ts) {}

    inline
    bool isLeaf() const { return true; };
    virtual LDIterator allChildren() = 0;
    virtual void insert(LeafData ld) = 0;
    virtual void remove(LeafData ld) = 0;
    void loadChildren(LDIterator children);
  };

  //These classes and methods are defined in SubstitutionTree_Nodes.cpp
  class UListLeaf;
  class SListIntermediateNode;
  class SListLeaf;
  class SetLeaf;
  static Leaf* createLeaf();
  static Leaf* createLeaf(TermList ts);
  static void ensureLeafEfficiency(Leaf** l);
  static IntermediateNode* createIntermediateNode();
  static IntermediateNode* createIntermediateNode(TermList ts);
  static void ensureIntermediateNodeEfficiency(IntermediateNode** inode);

  struct IsPtrToVarNodeFn
  {
    DECL_RETURN_TYPE(bool);
    bool operator()(Node** n)
    {
      return (*n)->term.isVar();
    }
  };

  class UListIntermediateNode
  : public IntermediateNode
  {
  public:
    inline
    UListIntermediateNode() : _nodes(0), _size(0) {}
    inline
    UListIntermediateNode(TermList ts) : IntermediateNode(ts), _nodes(0), _size(0) {}
    ~UListIntermediateNode()
    {
      if(_nodes) {
        _nodes->destroyWithDeletion();
      }
    }

    void makeEmpty()
    {
      IntermediateNode::makeEmpty();
      if(_nodes) {
        _nodes->destroy();
        _nodes=0;
      }
    }

    NodeAlgorithm algorithm() const { return UNSORTED_LIST; }
    bool isEmpty() const { return !_nodes; }
    int size() const { return _size; }
    NodeIterator allChildren()
    { return pvi( NodeList::PtrIterator(_nodes)); }

    NodeIterator variableChildren()
    {
      return pvi( getFilteredIterator(NodeList::PtrIterator(_nodes),
  	    IsPtrToVarNodeFn()) );
    }
    Node** childByTop(TermList t, bool canCreate);
    void remove(TermList t);

    CLASS_NAME("SubstitutionTree::UListIntermediateNode");
    USE_ALLOCATOR(UListIntermediateNode);

    NodeList* _nodes;
    int _size;
  };

  class SListIntermediateNode
  : public IntermediateNode
  {
  public:
    SListIntermediateNode() {}
    SListIntermediateNode(TermList ts) : IntermediateNode(ts) {}
    ~SListIntermediateNode()
    {
      NodeSkipList::Iterator nit(_nodes);
      while(nit.hasNext()) {
        delete nit.next();
      }
    }

    void makeEmpty()
    {
      IntermediateNode::makeEmpty();
      while(!_nodes.isEmpty()) {
        _nodes.pop();
      }
    }

    static SListIntermediateNode* assimilate(IntermediateNode* orig);

    inline
    NodeAlgorithm algorithm() const { return SKIP_LIST; }
    inline
    bool isEmpty() const { return _nodes.isEmpty(); }
  #if VDEBUG
    int size() const { return _nodes.size(); }
  #endif
    inline
    NodeIterator allChildren()
    {
      return pvi( NodeSkipList::PtrIterator(_nodes) );
    }
    inline
    NodeIterator variableChildren()
    {
      return pvi( getWhileLimitedIterator(
  		    NodeSkipList::PtrIterator(_nodes),
  		    IsPtrToVarNodeFn()) );
    }
    Node** childByTop(TermList t, bool canCreate)
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
    void remove(TermList t)
    {
      _nodes.remove(t);
    }

    CLASS_NAME("SubstitutionTree::SListIntermediateNode");
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

  struct SpecVarComparator
  {
    inline
    static Comparison compare(unsigned v1, unsigned v2)
    { return Int::compare(v2, v1); }
    inline
    static unsigned max()
    { return 0u; }
  };

  //Using BinaryHeap as a BindingQueue leads to about 30% faster insertion,
  //that when SkipList is used.
  typedef BinaryHeap<Binding,Binding::Comparator> BindingQueue;
  //typedef SkipList<Binding,Binding::Comparator> BindingQueue;
//  typedef SkipList<unsigned,SpecVarComparator> SpecVarQueue;
  typedef BinaryHeap<unsigned,SpecVarComparator> SpecVarQueue;

  void getBindings(Term* t, BindingQueue& bq);

  void insert(Node** node,BindingQueue& binding,LeafData ld);
  void remove(Node** node,BindingQueue& binding,LeafData ld);

  /** Number of top-level nodes */
  int _numberOfTopLevelNodes;
  /** Number of the next variable */
  int _nextVar;
  /** Array of nodes */
  Node** _nodes;

  class LeafIterator
  : public IteratorCore<Leaf*>
  {
  public:
    LeafIterator(SubstitutionTree* st)
    : _nextRootPtr(st->_nodes), _afterLastRootPtr(st->_nodes+st->_numberOfTopLevelNodes),
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

  /**
   * Class that supports matching operations required by
   * retrieval of generalizations in substitution trees.
   */
  class GenMatcher
  {
  public:
    GenMatcher(Term* query);
    ~GenMatcher();
    void bindSpecialVar(unsigned var, TermList term)
    {
      ALWAYS(_specVars->insert(var,term));
      _specVarQueue->insert(var);
    }
    TermList getNextSpecVarBinding()
    { return _specVars->get(_specVarQueue->top()); }
    bool matchNext(TermList nodeTerm);
    void backtrack();

    ResultSubstitutionSP getSubstitution(Renaming* resultNormalizer,
	    Renaming* queryDenormalizer);
  private:
    typedef DHMap<unsigned,TermList, IdentityHash<unsigned> > BindingMap;
    typedef Stack<unsigned> VarStack;
    static const unsigned BACKTRACK_SEPARATOR=0xFFFFFFFF;


    struct Binder;
    struct Applicator;
    class Substitution;
    struct MatchBacktrackObject;

    VarStack _boundVars;
    VarStack _poppedSpecVars;
    VarStack _poppedSpecVarIndexes;
    VarStack _insertedSpecVarIndexes;

    SpecVarQueue* _specVarQueue;
    BindingMap* _specVars;
    unsigned _maxVar;
    ArrayMap<TermList>* _bindings;
  };

  class FastGeneralizationsIterator
  : public IteratorCore<QueryResult>
  {
  public:
    FastGeneralizationsIterator(Node* root, Term* query, bool retrieveSubstitution, bool reversed=false);

    bool hasNext();
    QueryResult next();
  protected:
    void createInitialBindings(Term* t);
    /**
     * For a binary comutative literal, creates initial bindings,
     * where the order of special variables is reversed.
     */
    void createReversedInitialBindings(Term* t);
    bool findNextLeaf();

  private:
    GenMatcher _subst;
    bool _literalRetrieval;
    bool _retrieveSubstitution;
    bool _inLeaf;
    LDIterator _ldIterator;

    Node* _root;
    Stack<NodeList*> _alternatives;
    Stack<NodeAlgorithm> _nodeTypes;

    Renaming _resultNormalizer;
    Renaming _queryDenormalizer;
  };


  class UnificationsIterator
  : public IteratorCore<QueryResult>
  {
  public:
    UnificationsIterator(Node* root, Term* query, bool retrieveSubstitution, bool reversed=false);
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
    void extractSpecialVariables(TermList t, BacktrackData& bd);


    static const int QUERY_BANK=0;
    static const int RESULT_BANK=1;
    static const int NORM_QUERY_BANK=2;
    static const int NORM_RESULT_BANK=3;

    MMSubstitution subst;
    SpecVarQueue svQueue;
  private:
    bool literalRetrieval;
    bool retrieveSubstitution;
    bool inLeaf;
    LDIterator ldIterator;
    Stack<NodeIterator> nodeIterators;
    Stack<BacktrackData> bdStack;
    bool clientBDRecording;
    BacktrackData clientBacktrackData;
    Renaming queryNormalizer;
  };


  class GeneralizationsIterator
  : public UnificationsIterator
  {
  public:
    GeneralizationsIterator(Node* root, Term* query, bool retrieveSubstitution, bool reversed=false)
    : UnificationsIterator(root, query, retrieveSubstitution, reversed) {};
  protected:
    virtual bool associate(TermList query, TermList node);
    virtual NodeIterator getNodeIterator(IntermediateNode* n);
  };

  class InstancesIterator
  : public UnificationsIterator
  {
  public:
    InstancesIterator(Node* root, Term* query, bool retrieveSubstitution, bool reversed=false)
    : UnificationsIterator(root, query, retrieveSubstitution, reversed) {};
  protected:
    virtual bool associate(TermList query, TermList node);
    virtual NodeIterator getNodeIterator(IntermediateNode* n);
  };

#if VDEBUG
public:
  static string nodeToString(Node* topNode);
  string toString() const;
  bool isEmpty() const;
#endif

}; // class SubstiutionTree

} // namespace Indexing

#endif

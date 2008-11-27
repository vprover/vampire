/**
 * @file SubstitutionTree.hpp
 * Defines class SubstitutionTree.
 *
 * @since 16/08/2008 flight Sydney-San Francisco
 */

#ifndef __SubstitutionTree__
#define __SubstitutionTree__

#include "../Forwards.hpp"

#include "../Lib/VirtualIterator.hpp"
#include "../Lib/Comparison.hpp"
#include "../Lib/Int.hpp"
#include "../Lib/Stack.hpp"
#include "../Lib/List.hpp"
#include "../Lib/SkipList.hpp"
#include "../Lib/BinaryHeap.hpp"
#include "../Lib/BacktrackData.hpp"

#include "../Kernel/DoubleSubstitution.hpp"
#include "../Kernel/MMSubstitution.hpp"
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
:public Index
{
public:
  SubstitutionTree(int nodes);
  ~SubstitutionTree();

  void insert(Literal* lit, Clause* cls);
  void remove(Literal* lit, Clause* cls);
  void insert(TermList* term, Clause* cls);
  void remove(TermList* term, Clause* cls);

  SLQueryResultIterator getComplementaryUnifications(Literal* lit)
  {
    UnificationsIterator* core=new UnificationsIterator();
    core->init(this, lit, true);
    return SLQueryResultIterator(core);
  }

  SLQueryResultIterator getGeneralizations(Literal* lit)
  {
    GeneralizationsIterator* core=new GeneralizationsIterator();
    core->init(this, lit, false);
    return SLQueryResultIterator(core);
  }

#if VDEBUG
  string toString() const;
  bool isEmpty() const;
#endif

private:

  inline
  int getRootNodeIndex(Literal* t, bool complementary=false)
  {
    if(complementary) {
      return (int)t->complementaryHeader();
    } else {
      return (int)t->header();
    }
  }

  inline
  int getRootNodeIndex(TermList* t)
  {
    ASS(!t->isSpecialVar());
    if(t->isVar()) {
      return _numberOfTopLevelNodes-1;
    } else {
      return (int)t->term()->functor();
    }
  }

  struct LeafData {
    LeafData(Clause* cls, void* d) : clause(cls), data(d) {}
    inline
    bool operator==(const LeafData& o)
    { return clause==o.clause && data==o.data; }

    Clause* clause;
    void* data;
  };
  typedef VirtualIterator<LeafData> LDIterator;

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
    virtual Node** childByTop(TermList* t, bool canCreate) = 0;
    /**
     * Remove child which points to node with top symbol of @b t.
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
    virtual LDIterator allChildren() = 0;
    virtual void insert(LeafData ld) = 0;
    virtual void remove(LeafData ld) = 0;
    void loadChildren(LDIterator children);
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

  struct SpecVarComparator
  {
    inline
    static Comparison compare(unsigned v1, unsigned v2)
    {
  	return Int::compare(v2, v1);
    }
  };

  //Using BinaryHeap as a BindingQueue leads to about 30% faster insertion,
  //that when SkipList is used.
  typedef BinaryHeap<Binding,Binding::Comparator> BindingQueue;
  //typedef SkipList<Binding,Binding::Comparator> BindingQueue;
  typedef SkipList<unsigned,SpecVarComparator> SpecVarQueue;
  typedef Stack<Binding> BindingStack;
  typedef Stack<const TermList*> TermStack;

  void getBindings(Term* t, BindingQueue& bq);
  void getBindings(TermList* ts, BindingQueue& bq)
  {
    if(ts->tag() == REF) {
      getBindings(ts->term(), bq);
    }
  }


  void insert(Node** node,BindingQueue& binding,LeafData ld);
  void remove(Node** node,BindingQueue& binding,LeafData ld);

  /** Number of top-level nodes */
  int _numberOfTopLevelNodes;
  /** Number of the next variable */
  int _nextVar;
  /** Array of nodes */
  Node** _nodes;

  class UnificationsIterator
  : public IteratorCore<SLQueryResult>
  {
  public:
    UnificationsIterator() : subst(), inLeaf(false), ldIterator(LDIterator::getEmpty()),
    	nodeIterators(4), bdStack(4), clientBDRecording(false) {}
    void init(SubstitutionTree* t, Literal* query, bool complementary);

    bool hasNext();
    SLQueryResult next();
  protected:
    virtual bool associate(TermList query, TermList node);
    virtual NodeIterator getNodeIterator(IntermediateNode* n);

    void createInitialBindings(Term* t);
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
  protected:
    virtual bool associate(TermList query, TermList node);
    virtual NodeIterator getNodeIterator(IntermediateNode* n);
  };


}; // class SubstiutionTree

class AtomicClauseSubstitutionTree
: public SubstitutionTree
{
public:
  AtomicClauseSubstitutionTree(int nodes) : SubstitutionTree(nodes) {};
protected:
  void onAddedToContainer(Clause* c)
  {
    unsigned clen=c->length();
    if(clen==1) {
      for(unsigned i=0; i<clen; i++) {
	insert((*c)[i], c);
      }
    }
  }

  void onRemovedFromContainer(Clause* c)
  {
    unsigned clen=c->length();
    if(clen==1) {
      for(unsigned i=0; i<clen; i++) {
	remove((*c)[i], c);
      }
    }
  }
};

class SimplifyingSubstitutionTree
: public SubstitutionTree
{
public:
  SimplifyingSubstitutionTree(int nodes) : SubstitutionTree(nodes) {};
protected:
  void onAddedToContainer(Clause* c)
  {
    unsigned clen=c->length();
    for(unsigned i=0; i<clen; i++) {
      insert((*c)[i], c);
    }
  }

  void onRemovedFromContainer(Clause* c)
  {
    unsigned clen=c->length();
    for(unsigned i=0; i<clen; i++) {
      remove((*c)[i], c);
    }
  }
};

} // namespace Indexing

#endif

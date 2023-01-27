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
#include "Lib/Recycler.hpp"
#include "Kernel/BottomUpEvaluation/TypedTermList.hpp"

#include "Kernel/RobSubstitution.hpp"
#include "Kernel/Renaming.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/OperatorType.hpp"
#include "Lib/Option.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/ApplicativeHelper.hpp"

#include "Lib/Allocator.hpp"

#include "Index.hpp"

#if VDEBUG
#include <iostream>
#endif


// TODO where should these go?
static constexpr int QUERY_BANK=0;
static constexpr int RESULT_BANK=1;
static constexpr int NORM_RESULT_BANK=3;
using namespace std;
using namespace Lib;
using namespace Kernel;

#define UARR_INTERMEDIATE_NODE_MAX_SIZE 4

template<class T>
struct OutputMultiline
{ 
  T const& self; 
  int indent; 

  template<class A>
  static void repeat(std::ostream& out, A const& c, int times) 
  { for (int i = 0; i < times; i++) out << c; };

  static void outputIndent(std::ostream& out, int cnt) { repeat(out, "    ", cnt); }
  void outputIndent(std::ostream& out) { outputIndent(out, indent); }
};

template<class T>
OutputMultiline<T> multiline(T const& self, int indent)
{ return { self, indent, }; }

#define REORDERING 1

namespace Indexing {

  namespace UnificationAlgorithms {
    class RobUnification { 
      Recycled<RobSubstitution> _subs;
    public:
      RobUnification() : _subs() {}
      using Unifier = RobSubstitutionSP; 

      bool associate(unsigned specialVar, TermList node, BacktrackData& bd)
      {
        CALL("SubstitutionTree::UnificationsIterator::associate");
        TermList query(specialVar, /* special */ true);
        return _subs->unify(query, QUERY_BANK, node, NORM_RESULT_BANK);
      }


      Unifier unifier() { return RobSubstitutionSP(&*_subs); }

      void bindQuerySpecialVar(unsigned var, TermList term, unsigned varBank)
      { _subs->bindSpecialVar(var, term, varBank); }

      void bdRecord(BacktrackData& bd) { _subs->bdRecord(bd); }
      void bdDone() { _subs->bdDone(); }

      void denormalize(Renaming& norm, unsigned NORM_RESULT_BANK,unsigned RESULT_BANK)
      { _subs->denormalize(norm, NORM_RESULT_BANK,RESULT_BANK); }

      TermList getSpecialVarTop(unsigned svar) 
      { return _subs->getSpecialVarTop(svar); }

      bool usesUwa() const { return false; }
    };
    // TODO change this
    using UnificationWithAbstraction = RobUnification;
  };


class SubstitutionTree;
std::ostream& operator<<(std::ostream& out, SubstitutionTree const& self);
std::ostream& operator<<(std::ostream& out, OutputMultiline<SubstitutionTree> const& self);

template<class Key> struct SubtitutionTreeConfig;

/**
 * Class of substitution trees. 
 *
 * We can either typed terms, or literals into a subtitution tree.
 * Classically we'd think of inserting/removing only one term t into a substitution tree. 
 * This can be understood as inserting the substitution { S0 -> t } into the tree.
 *
 * In general we can insertt a substitution with more than just this one binding. 
 * This is what we do in order to store the sort of variables, and in order to insert all the arguments of a literal:
 * - For a term t of sort s we insert { S0 -> t; S1 -> s }
 * - For literals (~)P(t0..tn) we insert { S0 -> t0 .. Sn -> tn }.
 * (Note that we do not check the predicate of the polarity of literals here. This happens in LiteralSubstitutionTree)
 */
class SubstitutionTree
{
  class IterCounter {
    public:
#if VDEBUG
    SubstitutionTree* _parent;

    IterCounter& operator=(IterCounter&& other) 
    { swap(other._parent, _parent); return *this; }

    IterCounter(IterCounter&& other) 
      : _parent(other._parent)
    { other._parent->_iteratorCnt++; }

    IterCounter(SubstitutionTree* parent) : _parent(parent) 
    { 
      _parent->_iteratorCnt++; 
    }
    ~IterCounter() {
      _parent->_iteratorCnt--;
    }
#else // VDEBUG
    IterCounter(SubstitutionTree* parent) {}
#endif 
  };
  friend class IterCounter;
public:
  static constexpr int QRS_QUERY_BANK = 0;
  static constexpr int QRS_RESULT_BANK = 1;
  CLASS_NAME(SubstitutionTree);
  USE_ALLOCATOR(SubstitutionTree);

  SubstitutionTree();
  SubstitutionTree(SubstitutionTree const&) = delete;

  virtual ~SubstitutionTree();

  friend std::ostream& operator<<(std::ostream& out, SubstitutionTree const& self);
  friend std::ostream& operator<<(std::ostream& out, OutputMultiline<SubstitutionTree> const& self);


//protected:

  struct LeafData {
    LeafData() {}

    LeafData(Clause* cls, Literal* literal, TypedTermList term, TermList extraTerm)
    : clause(cls), literal(literal), term(term), sort(term.sort()), extraTerm(extraTerm) {}
    LeafData(Clause* cls, Literal* literal, TypedTermList term)
    : clause(cls), literal(literal), term(term), sort(term.sort()) { extraTerm.makeEmpty();}

    LeafData(Clause* cls, Literal* literal, TermList term, TermList extraTerm)
    : clause(cls), literal(literal), term(term), extraTerm(extraTerm) { sort.makeEmpty();}
    LeafData(Clause* cls, Literal* literal, TermList term)
    : clause(cls), literal(literal), term(term) { extraTerm.makeEmpty(); sort.makeEmpty(); }

    LeafData(Clause* cls, Literal* literal)
    : clause(cls), literal(literal) { term.makeEmpty(); sort.makeEmpty(), extraTerm.makeEmpty(); }
    inline
    bool operator==(const LeafData& o)
    { return clause==o.clause && literal==o.literal && term==o.term; }

    Clause* clause;
    Literal* literal;
    TermList term;
    TermList sort;
    // In some higher-order use cases, we want to store a different term 
    // in the leaf to the indexed term. extraTerm is used for this purpose.
    // In all other situations it is empty
    TermList extraTerm;

    vstring toString(){
      vstring ret = "LD " + literal->toString();// + " in " + clause->literalsOnlyToString();
      if(!term.isEmpty()){ ret += " with " +term.toString(); }
      return ret;
    }

  };
  typedef VirtualIterator<LeafData&> LDIterator;

  template<class Unifier>
  struct QueryResult {
    LeafData const* data; 
    Unifier unif;

    QueryResult(LeafData const& ld, Unifier unif) : data(&ld), unif(std::move(unif)) {}
  };
  template<class Unifier>
  static QueryResult<Unifier>  queryResult(LeafData const& ld, Unifier unif) 
  { return QueryResult<Unifier>(ld, std::move(unif)); }

  template<class I> using QueryResultIter = VirtualIterator<QueryResult<typename I::Unifier>>;
  // TODO get rid of me
  using RSQueryResult = QueryResult<ResultSubstitutionSP>;
  // TODO get rid of me
  using RSQueryResultIter = VirtualIterator<QueryResult<ResultSubstitutionSP>>;
  // TODO make const function
  template<class I, class TermOrLit, class... Args> 
  QueryResultIter<I> iterator(TermOrLit query, bool retrieveSubstitutions, bool reversed, Args... args)
  {
    CALL("TermSubstitutionTree::iterator");
    return _root == nullptr 
      ? QueryResultIter<I>::getEmpty()
      : pvi(iterTraits(I(this, _root, query, retrieveSubstitutions, reversed, std::move(args)...))
                    // .filter([handler](auto r) { 
                    //   if (handler == nullptr) return true;
                    //   auto& s = *r.subst->tryGetRobSubstitution();
                    //   return r.constr->iter().all([&](auto& c) { return handler->recheck(c.lhs(s), c.rhs(s)); });
                    // })
                    );
  }

  class LDComparator
  {
  public:
    inline
    static Comparison compare(const LeafData& ld1, const LeafData& ld2)
    {
      CALL("SubstitutionTree::LDComparator::compare");

      if(ld1.clause && ld2.clause && ld1.clause!=ld2.clause) {
        ASS_NEQ(ld1.clause->number(), ld2.clause->number());
        return (ld1.clause->number()<ld2.clause->number()) ? LESS : GREATER;
      }
      Comparison res;
      if(ld1.literal && ld2.literal && ld1.literal!=ld2.literal) {
        res = (ld1.literal->getId()<ld2.literal->getId())? LESS : GREATER;
      } else {
        ASS_EQ(ld1.clause,ld2.clause);
        ASS_EQ(ld1.literal,ld2.literal);

        if (ld1.term.isEmpty()) {
          ASS(ld2.term.isEmpty());
          res = EQUAL;
        } else {
          if (ld1.term.isVar()) {
            if (ld2.term.isVar()) {
              unsigned var1 = ld1.term.var();
              unsigned var2 = ld2.term.var();
              res=(var1<var2)? LESS : (var1>var2)? GREATER : EQUAL;
            }
            else{
              res = LESS;
            }
          } else {
            if (ld2.term.isVar()) {
              res = GREATER;
            } else {
              unsigned id1 = ld1.term.term()->getId();
              unsigned id2 = ld2.term.term()->getId();
              res=(id1<id2)? LESS : (id1>id2)? GREATER : EQUAL;
            }
          }
        }
      }
      return res;
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
    friend std::ostream& operator<<(ostream& out, OutputMultiline<Node> const& self) 
    { self.self.output(out, /* multiline = */ true, self.indent); return out; }
    friend std::ostream& operator<<(ostream& out, Node const& self) 
    { self.output(out, /* multiline = */ false, /* indent */ 0); return out; }
    inline
    Node() { term.makeEmpty(); }
    inline
    Node(TermList ts) : term(ts) { }
    virtual ~Node();
    /** True if a leaf node */
    virtual bool isLeaf() const = 0;
    virtual bool isEmpty() const = 0;
    /**
     * Return number of elements held in the node.
     *
     * Descendant classes should override this method.
     */
    virtual int size() const { NOT_IMPLEMENTED; }
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
    virtual void assertValid() const {};
#endif

    /** term at this node */
    TermList term;

    virtual void output(std::ostream& out, bool multiline, int indent) const = 0;
  };


  typedef VirtualIterator<Node**> NodeIterator;
  class IntermediateNode;
    
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

    virtual void mightExistAsTop(TermList t) {
    }

    void loadChildren(NodeIterator children);

    const unsigned childVar;

    virtual void output(std::ostream& out, bool multiline, int indent) const override;
  }; // class SubstitutionTree::IntermediateNode

    struct NotTop
    {
        NotTop(unsigned t) : top(t) {};
        bool operator()(TermList t){
            return t.term()->functor()!=top;
        }
    private:
        unsigned top;
    };
    

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
    virtual LDIterator allChildren() = 0;
    virtual void insert(LeafData ld) = 0;
    virtual void remove(LeafData ld) = 0;
    void loadChildren(LDIterator children);
    virtual void output(std::ostream& out, bool multiline, int indent) const override;
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
	destroyChildren();
      }
    }

    void removeAllChildren()
    {
      _size=0;
      _nodes[0]=0;
    }

    NodeAlgorithm algorithm() const { return UNSORTED_LIST; }
    bool isEmpty() const { return !_size; }
    int size() const { return _size; }
    NodeIterator allChildren()
    { return pvi( PointerPtrIterator<Node*>(&_nodes[0],&_nodes[_size]) ); }

    NodeIterator variableChildren()
    {
      return pvi( getFilteredIterator(PointerPtrIterator<Node*>(&_nodes[0],&_nodes[_size]),
  	    IsPtrToVarNodeFn()) );
    }
    virtual Node** childByTop(TermList t, bool canCreate);
    void remove(TermList t);

#if VDEBUG
    virtual void assertValid() const
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
	destroyChildren();
      }
    }

    void removeAllChildren()
    {
      while(!_nodes.isEmpty()) {
        _nodes.pop();
      }
    }

    static IntermediateNode* assimilate(IntermediateNode* orig);

    inline
    NodeAlgorithm algorithm() const { return SKIP_LIST; }
    inline
    bool isEmpty() const { return _nodes.isEmpty(); }
    int size() const { return _nodes.size(); }
#if VDEBUG
    virtual void assertValid() const
    {
      ASS_ALLOC_TYPE(this,"SubstitutionTree::SListIntermediateNode");
    }
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
    virtual Node** childByTop(TermList t, bool canCreate)
    {
      CALL("SubstitutionTree::SListIntermediateNode::childByTop");

      Node** res;
      bool found=_nodes.getPosition(t,res,canCreate);
      if(!found) {
        if(canCreate) {
          mightExistAsTop(t);
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

  typedef DHMap<unsigned,TermList,IdentityHash,DefaultHash> BindingMap;
  //Using BinaryHeap as a BindingQueue leads to about 30% faster insertion,
  //that when SkipList is used.
  typedef BinaryHeap<Binding,Binding::Comparator> BindingQueue;
  typedef BinaryHeap<unsigned,SpecVarComparator> SpecVarQueue;
  typedef Stack<unsigned> VarStack;

  void getBindingsArgBindings(Term* t, BindingMap& binding);

  Leaf* findLeaf(BindingMap& svBindings)
  { ASS(!_root || !_root->isLeaf() )
    return _root ? findLeaf(_root, svBindings) : nullptr; }

  Leaf* findLeaf(Node* root, BindingMap& svBindings);

  // TODO document
  void setKey(TypedTermList const& term, LeafData& ld)
  {
    ASS_EQ(ld.term, term)
    ld.sort = term.sort();
  }

  void setKey(TermList const& term, LeafData& ld)
  {
    ASS_EQ(ld.term, term)
    if (term.isTerm()) {
      ld.sort = SortHelper::getResultSort(term.term());
    }
  }


  void setKey(Literal* literal, LeafData &ld)
  { 
    ASS_EQ(ld.literal, literal); 
    if (literal->isEquality()) 
      ld.sort = SortHelper::getEqualityArgumentSort(literal);
  }


  template<class Key>
  void handle(Key const& key, LeafData ld, bool doInsert)
  {
    auto norm = Renaming::normalize(key);
    Recycled<BindingMap> bindings;
    setKey(key, ld);
    createBindings(norm, /* reversed */ false,
        [&](auto var, auto term) { 
          bindings->insert(var, term);
          _nextVar = max(_nextVar, (int)var + 1);
        });
    if (doInsert) insert(*bindings, ld);
    else          remove(*bindings, ld);
  }

private:
  void insert(BindingMap& binding,LeafData ld);
  void remove(BindingMap& binding,LeafData ld);

  /** Number of the next variable */
  int _nextVar;
  Node* _root;
#if VDEBUG
  bool _tag;
#endif
public:
#if VDEBUG
  // Tags are used as a debug tool to turn debugging on for a particular instance
  virtual void markTagged(){ _tag=true;}
#endif

  class RenamingSubstitution 
  : public ResultSubstitution 
  {
  public:
    Recycled<Renaming> _query;
    Recycled<Renaming> _result;
    RenamingSubstitution(): _query(), _result() {}
    virtual ~RenamingSubstitution() override {}
    virtual TermList applyToQuery(TermList t) final override { return _query->apply(t); }
    virtual Literal* applyToQuery(Literal* l) final override { return _query->apply(l); }
    virtual TermList applyToResult(TermList t) final override { return _result->apply(t); }
    virtual Literal* applyToResult(Literal* l) final override { return _result->apply(l); }

    virtual TermList applyTo(TermList t, unsigned index) final override { ASSERTION_VIOLATION; }
    virtual Literal* applyTo(Literal* l, unsigned index) final override { NOT_IMPLEMENTED; }

    virtual size_t getQueryApplicationWeight(TermList t) final override { return t.weight(); }
    virtual size_t getQueryApplicationWeight(Literal* l) final override  { return l->weight(); }
    virtual size_t getResultApplicationWeight(TermList t) final override { return t.weight(); }
    virtual size_t getResultApplicationWeight(Literal* l) final override { return l->weight(); }

    void output(std::ostream& out) const final override
    { out << "{ _query: " << _query << ", _result: " << _result << " }"; }
  };

  template<class Query>
  bool generalizationExists(Query query)
  {
    return _root == nullptr 
      ? false
      : FastGeneralizationsIterator(this, _root, query, /* retrieveSubstitutions */ false, /* reversed */ false).hasNext();
  }

  template<class Query>
  RSQueryResultIter getVariants(Query query, bool retrieveSubstitutions)
  {
    CALL("LiteralSubstitutionTree::getVariants");


    RenamingSubstitution* renaming = retrieveSubstitutions ? new RenamingSubstitution() : nullptr;
    ResultSubstitutionSP resultSubst = retrieveSubstitutions ? ResultSubstitutionSP(renaming) : ResultSubstitutionSP();

    Query normQuery;
    if (retrieveSubstitutions) {
      renaming->_query->normalizeVariables(query);
      normQuery = renaming->_query->apply(query);
    } else {
      normQuery = Renaming::normalize(query);
    }

    Recycled<BindingMap> svBindings;
    createBindings(normQuery, /* reversed */ false,
        [&](auto v, auto t) { {
          _nextVar = max<int>(_nextVar, v + 1); // TODO do we need this line?
          svBindings->insert(v, t);
        } });
    Leaf* leaf = findLeaf(*svBindings);
    if(leaf==0) {
      return RSQueryResultIter::getEmpty();
    } else {
      return pvi(iterTraits(leaf->allChildren())
        .map([retrieveSubstitutions, renaming, resultSubst](LeafData ld) 
          {
            ResultSubstitutionSP subs;
            if (retrieveSubstitutions) {
              renaming->_result->reset();
              renaming->_result->normalizeVariables(SubtitutionTreeConfig<Query>::getKey(ld));
              subs = resultSubst;
            }
            return queryResult(ld, subs);
          }));
    }
  }

  class LeafIterator
  {
  public:
    LeafIterator(LeafIterator&&) = default;
    LeafIterator& operator=(LeafIterator&&) = default;
    DECL_ELEMENT_TYPE(Leaf*);
    LeafIterator(SubstitutionTree* st);
    bool hasNext();
    Leaf* next();
  private:
    void skipToNextLeaf();
    Node* _curr;
    Stack<NodeIterator> _nodeIterators;
  };



   /**
   * Class that supports matching operations required by
   * retrieval of generalizations in substitution trees.
   */
  class GenMatcher
  {
    static unsigned weight(Literal* l) { return l->weight(); }
    static unsigned weight(TermList t) { return  t.weight(); }
  public:
    GenMatcher(GenMatcher&&) = default;
    GenMatcher& operator=(GenMatcher&&) = default;

    /**
     * @b nextSpecVar Number higher than any special variable present in the tree.
     * 	It's used to determine size of the array that stores bindings of
     * 	special variables.
     */
    template<class TermOrLit>
    GenMatcher(TermOrLit query, unsigned nextSpecVar)
      : _boundVars()
      , _specVars()
      , _maxVar(weight(query) - 1)
      , _bindings()
    {
      if(_specVars->size()<nextSpecVar) {
        //_specVars can get really big, but it was introduced instead of hash table
        //during optimizations, as it raised performance by abour 5%.
        _specVars->ensure(max(static_cast<unsigned>(_specVars->size()*2), nextSpecVar));
      }
      _bindings->ensure(weight(query));
    }



    CLASS_NAME(SubstitutionTree::GenMatcher);
    USE_ALLOCATOR(GenMatcher);

    /**
     * Bind special variable @b var to @b term. This method
     * should be called only before any calls to @b matchNext()
     * and @b backtrack().
     */
    void bindSpecialVar(unsigned var, TermList term)
    {
      (*_specVars)[var]=term;
    }
    /**
     * Return term bound to special variable @b specVar
     */
    TermList getSpecVarBinding(unsigned specVar)
    { return (*_specVars)[specVar]; }

    bool matchNext(unsigned specVar, TermList nodeTerm, bool separate=true);
    bool matchNextAux(TermList queryTerm, TermList nodeTerm, bool separate=true);
    void backtrack();
    bool tryBacktrack();

    ResultSubstitutionSP getSubstitution(Renaming* resultNormalizer);

    int getBSCnt()
    {
      int res=0;
      VarStack::Iterator vsit(*_boundVars);
      while(vsit.hasNext()) {
    if(vsit.next()==BACKTRACK_SEPARATOR) {
      res++;
    }
      }
      return res;
    }

  protected:
    static const unsigned BACKTRACK_SEPARATOR=0xFFFFFFFF;

    struct Binder;
    struct Applicator;
    class Substitution;

    Recycled<VarStack> _boundVars;
    Recycled<DArray<TermList>, NoReset> _specVars;

    /**
     * Inheritors must assign the maximal possible number of an ordinary
     * variable that can be bound during the retrievall process.
     */
    unsigned _maxVar;

    /**
     * Inheritors must ensure that the size of this map will
     * be at least @b _maxVar+1
     */
    Recycled<ArrayMap<TermList>> _bindings;
  };

  // TODO document
  template<class BindingFunction>
  void createBindings(TypedTermList term, bool reversed, BindingFunction bindSpecialVar)
  {
    bindSpecialVar(0, term);
    bindSpecialVar(1, term.sort());
  }

  // TODO document
  template<class BindingFunction>
  void createBindings(TermList term, bool reversed, BindingFunction bindSpecialVar)
  { 
    bindSpecialVar(0, term); 
    if (term.isTerm())
      bindSpecialVar(1, SortHelper::getResultSort(term.term()));
  }

  template<class BindingFunction>
  void createBindings(Literal* lit, bool reversed, BindingFunction bindSpecialVar)
  {
    if (lit->isEquality()) {

      if (reversed) {
        bindSpecialVar(1,*lit->nthArgument(0));
        bindSpecialVar(0,*lit->nthArgument(1));
      } else {
        bindSpecialVar(0,*lit->nthArgument(0));
        bindSpecialVar(1,*lit->nthArgument(1));
      }

      bindSpecialVar(2, SortHelper::getEqualityArgumentSort(lit));

    } else if(reversed) {
      ASS(lit->commutative());
      ASS_EQ(lit->arity(),2);

      bindSpecialVar(1,*lit->nthArgument(0));
      bindSpecialVar(0,*lit->nthArgument(1));

    } else if (lit->arity() == 0) {
      // insert a dummy term
      bindSpecialVar(0, TermList::var(0));

    } else {

      TermList* args=lit->args();
      int nextVar = 0;
      while (! args->isEmpty()) {
        unsigned var = nextVar++;
        bindSpecialVar(var,*args);
        args = args->next();
      }
    }
  }

  /**
   * Iterator, that yields generalizations of given term/literal.
   */
  class FastGeneralizationsIterator
  {
  public:
    FastGeneralizationsIterator(FastGeneralizationsIterator&&) = default;
    FastGeneralizationsIterator& operator=(FastGeneralizationsIterator&&) = default;
    DECL_ELEMENT_TYPE(RSQueryResult);
    using Unifier = ResultSubstitutionSP;
    /**
     * @b nextSpecVar is the first unassigned special variable. Is being used
     * 	to determine size of array, that stores special variable bindings.
     * 	(To maximize performance, a DArray object is being used instead
     * 	of hash map.)
     * If @b reversed If true, parameters of supplied binary literal are
     * 	reversed. (useful for retrieval commutative terms)
     */
    template<class TermOrLit>
    FastGeneralizationsIterator(SubstitutionTree* parent, Node* root, TermOrLit query, bool retrieveSubstitution, bool reversed)
      : _literalRetrieval(std::is_same<TermOrLit, Literal*>::value)
      , _retrieveSubstitution(retrieveSubstitution)
      , _inLeaf(false)
      , _subst(query,parent->_nextVar)
      , _ldIterator(LDIterator::getEmpty())
      , _resultNormalizer()
      , _root(root)
      , _alternatives()
      , _specVarNumbers()
      , _nodeTypes()
      , _iterCounter(parent)
    {
      CALL("SubstitutionTree::FastGeneralizationsIterator::FastGeneralizationsIterator");
      ASS(root);
      ASS(!root->isLeaf());

      parent->createBindings(query, reversed,
          [&](unsigned var, TermList t) { _subst.bindSpecialVar(var, t); });
    }

    RSQueryResult next();
    bool hasNext();
  protected:

    bool findNextLeaf();
    bool enterNode(Node*& node);

    /** We are retrieving generalizations of a literal */
    bool _literalRetrieval;
    /** We should include substitutions in the results */
    bool _retrieveSubstitution;
    /** The iterator is currently in a leaf
     *
     * This is false in the beginning when it is in the root */
    bool _inLeaf;

    GenMatcher _subst;

    LDIterator _ldIterator;

    Recycled<Renaming> _resultNormalizer;

    Node* _root;

    Recycled<Stack<void*>> _alternatives;
    Recycled<Stack<unsigned>> _specVarNumbers;
    Recycled<Stack<NodeAlgorithm>> _nodeTypes;
    IterCounter _iterCounter;
  };


  /**
   * Class that supports matching operations required by
   * retrieval of generalizations in substitution trees.
   */
  class InstMatcher 
  {
  public:
    void reset()
    {
      _boundVars.reset();
      _bindings.reset();
      _derefBindings.reset();
    }

    CLASS_NAME(SubstitutionTree::InstMatcher);
    USE_ALLOCATOR(InstMatcher);

    struct TermSpec
    {
      TermSpec() : q(false) {
      #if VDEBUG
        t.makeEmpty();
      #endif
      }
      TermSpec(bool q, TermList t)
      : q(q), t(t)
      {
        CALL("SubstitutionTree::InstMatcher::TermSpec::TermSpec");

        //query does not contain special vars
        ASS(!q || !t.isTerm() || t.term()->shared());
        ASS(!q || !t.isSpecialVar());
      }

      vstring toString()
      {
        CALL("SubstitutionTree::InstMatcher::TermSpec::toString");
        return (q ? "q|" : "n|")+t.toString();
      }

      /**
       * Return true if the @b t field can be use as a binding for a query
       * term variable in the retrieved substitution
       */
      bool isFinal()
      {
        //the fact that a term is shared means it does not contain any special variables
        return q
      ? (t.isTerm() && t.term()->ground())
      : (t.isOrdinaryVar() || (t.isTerm() && t.term()->shared()) );
      }

      bool q;
      TermList t;
    };

    /**
     * Bind special variable @b var to @b term
     *
     * This method should be called only before any calls to @b matchNext()
     * and @b backtrack().
     */
    void bindSpecialVar(unsigned var, TermList term)
    {
      CALL("SubstitutionTree::InstMatcher::bindSpecialVar");
      ASS_EQ(getBSCnt(), 0);

      ALWAYS(_bindings.insert(TermList(var,true),TermSpec(true,term)));
    }

    bool isSpecVarBound(unsigned specVar)
    {
      return _bindings.find(TermList(specVar,true));
    }

    /** Return term bound to special variable @b specVar */
    TermSpec getSpecVarBinding(unsigned specVar)
    {
      TermSpec res=_bindings.get(TermList(specVar,true));

      return res;
    }

    bool findSpecVarBinding(unsigned specVar, TermSpec& res)
    {
      return _bindings.find(TermList(specVar,true), res);
    }

    bool matchNext(unsigned specVar, TermList nodeTerm, bool separate=true);
    bool matchNextAux(TermList queryTerm, TermList nodeTerm, bool separate=true);

    void backtrack();
    bool tryBacktrack();
    ResultSubstitutionSP getSubstitution(Renaming* resultDenormalizer);

    int getBSCnt()
    {
      int res=0;
      TermStack::Iterator vsit(_boundVars);
      while(vsit.hasNext()) {
        if(vsit.next().isEmpty()) {
    res++;
        }
      }
      return res;
    }

    void onLeafEntered()
    {
      _derefBindings.reset();
    }

  private:

    class Substitution;

    TermList derefQueryBinding(unsigned var);

    bool isBound(TermList var)
    {
      CALL("SubstitutionTree::InstMatcher::isBound");
      ASS(var.isVar());

      return _bindings.find(var);
    }
    void bind(TermList var, TermSpec trm)
    {
      CALL("SubstitutionTree::InstMatcher::bind");
      ASS(!var.isOrdinaryVar() || !trm.q); //we do not bind ordinary vars to query terms

      ALWAYS(_bindings.insert(var, trm));
      _boundVars.push(var);
    }

    TermSpec deref(TermList var);

    typedef DHMap<TermList, TermSpec> BindingMap;
    typedef Stack<TermList> TermStack;

    /** Stacks of bindings made on each backtrack level. Backtrack
     * levels are separated by empty terms. */
    TermStack _boundVars;

    BindingMap _bindings;

    /**
     * A cache for bindings of variables to result terms
     *
     * The map is reset whenever we enter a new leaf
     */
    DHMap<TermList,TermList> _derefBindings;

    struct DerefTask
    {
      DerefTask(TermList var) : var(var) { trm.t.makeEmpty(); }
      DerefTask(TermList var, TermSpec trm) : var(var), trm(trm) {}
      TermList var;
      TermSpec trm;
      bool buildDerefTerm() { return trm.t.isNonEmpty(); };
    };

    struct DerefApplicator
    {
      DerefApplicator(InstMatcher* im, bool query) : query(query), im(im) {}
      TermList apply(unsigned var)
      {
        CALL("SubstitutionTree::InstMatcher::DerefApplicator::apply");
        if(query) {
    return im->_derefBindings.get(TermList(var, false));
        }
        else {
    return TermList(var, false);
        }
      }
      TermList applyToSpecVar(unsigned specVar)
      {
        CALL("SubstitutionTree::InstMatcher::DerefApplicator::applyToSpecVar");
        ASS(!query);

        return im->_derefBindings.get(TermList(specVar, true));
      }
    private:
      bool query;
      InstMatcher* im;
    };
  };

  /**
   * Iterator, that yields generalizations of given term/literal.
   */
  class FastInstancesIterator
  {
  public:
    FastInstancesIterator(FastInstancesIterator&&) = default;
    FastInstancesIterator& operator=(FastInstancesIterator&&) = default;
    DECL_ELEMENT_TYPE(RSQueryResult);
    using Unifier = ResultSubstitutionSP;

    /**
     * @b nextSpecVar is the first unassigned special variable. Is being used
     * 	to determine size of array, that stores special variable bindings.
     * 	(To maximize performance, a DArray object is being used instead
     * 	of hash map.)
     * If @b reversed If true, parameters of supplied binary literal are
     * 	reversed. (useful for retrieval commutative terms)
     */
    template<class TermOrLit>
    FastInstancesIterator(SubstitutionTree* parent, Node* root, TermOrLit query, bool retrieveSubstitution, bool reversed)
      : _literalRetrieval(std::is_same<TermOrLit, Literal*>::value)
      , _retrieveSubstitution(retrieveSubstitution)
      , _inLeaf(false)
      , _ldIterator(LDIterator::getEmpty())
      , _root(root)
      , _alternatives()
      , _specVarNumbers()
      , _nodeTypes()
      , _iterCounter(parent)
    {
      CALL("SubstitutionTree::FastInstancesIterator::FastInstancesIterator");
      ASS(root);
      ASS(!root->isLeaf());

      parent->createBindings(query, reversed,
          [&](unsigned var, TermList t) { _subst->bindSpecialVar(var, t); });
    }

    bool hasNext();
    RSQueryResult next();
  protected:
    bool findNextLeaf();

    bool enterNode(Node*& node);

  private:

    bool _literalRetrieval;
    bool _retrieveSubstitution;
    bool _inLeaf;
    LDIterator _ldIterator;

    Recycled<InstMatcher> _subst;

    Renaming _resultDenormalizer;
    Node* _root;

    Recycled<Stack<void*>> _alternatives;
    Recycled<Stack<unsigned>> _specVarNumbers;
    Recycled<Stack<NodeAlgorithm>> _nodeTypes;
    IterCounter _iterCounter;
  };

  template<class UnificationAlgorithm>
  class UnificationsIterator final
  {
  public:
    UnificationsIterator(UnificationsIterator&&) = default;
    UnificationsIterator& operator=(UnificationsIterator&&) = default;
    using Unifier = Option<typename UnificationAlgorithm::Unifier>;
    DECL_ELEMENT_TYPE(QueryResult<Unifier>);

    template<class TermOrLit, class...AlgoArgs>
    UnificationsIterator(SubstitutionTree* parent, Node* root, TermOrLit query, bool retrieveSubstitution, bool reversed, AlgoArgs... args)
      : _algo(std::move(args)...)
      , _svStack()
      , _literalRetrieval(std::is_same<TermOrLit, Literal*>::value)
      , _retrieveSubstitution(retrieveSubstitution)
      , _inLeaf(false)
      , _ldIterator(LDIterator::getEmpty())
      , _nodeIterators()
      , _bdStack()
      , _clientBDRecording(false)
      , _parentIterCntr(parent)
#if VDEBUG
      , _tag(parent->_tag)
#endif
    {
#define DEBUG_QUERY(...) // DBG(__VA_ARGS__)
      CALL("SubstitutionTree::UnificationsIterator::UnificationsIterator");

      if(!root) {
        return;
      }

      parent->createBindings(query, reversed, 
          [&](unsigned var, TermList t) { _algo.bindQuerySpecialVar(var, t, QUERY_BANK); });
      DEBUG_QUERY("query: ", _abstractingUnifier.subs())


      BacktrackData bd;
      enter(root, bd);
      bd.drop();
    }


    ~UnificationsIterator()
    {
      if(_clientBDRecording) {
        _algo.bdDone();
        _clientBDRecording=false;
        _clientBacktrackData.backtrack();
      }
      if (_bdStack) 
        while(_bdStack->isNonEmpty()) {
          _bdStack->pop().backtrack();
        }
    }

    bool hasNext()
    {
      CALL("SubstitutionTree::UnificationsIterator::hasNext");

      if(_clientBDRecording) {
        _algo.bdDone();
        _clientBDRecording=false;
        _clientBacktrackData.backtrack();
      }

      while(!_ldIterator.hasNext() && findNextLeaf()) {}
      return _ldIterator.hasNext();
    }

    QueryResult<Unifier> next()
    {
      CALL("SubstitutionTree::UnificationsIterator::next");

      while(!_ldIterator.hasNext() && findNextLeaf()) {}
      ASS(_ldIterator.hasNext());

      ASS(!_clientBDRecording);

      LeafData& ld=_ldIterator.next();

      return queryResult(ld,
        someIf(_retrieveSubstitution, [&](){
          Renaming normalizer;
          if(_literalRetrieval) {
            normalizer.normalizeVariables(ld.literal);
          } else {
            normalizer.normalizeVariables(ld.term);
            if (ld.sort.isNonEmpty()) {
              normalizer.normalizeVariables(ld.sort);
            }
          }

          ASS(_clientBacktrackData.isEmpty());
          _algo.bdRecord(_clientBacktrackData);
          _clientBDRecording=true;

          _algo.denormalize(normalizer,NORM_RESULT_BANK,RESULT_BANK);

          return _algo.unifier();
       }));
    }

  private:
    // bool associate(unsigned specialVar, TermList node, BacktrackData& bd)
    // {
    //   CALL("SubstitutionTree::UnificationsIterator::associate");
    //   TermList query(specialVar, /* special */ true);
    //   return _abstractingUnifier.unify(query, QUERY_BANK, node, NORM_RESULT_BANK);
    // }

    NodeIterator getNodeIterator(IntermediateNode* n)
    {
      CALL("SubstitutionTree::UnificationsIterator::getNodeIterator");

      // TODO rename usesUwa to something more self explanatory
      if (_algo.usesUwa()) {
        return n->allChildren();
      }

      unsigned specVar=n->childVar;
      // TermList qt = _abstractingUnifier.subs().getSpecialVarTop(specVar);
      // TODO should this function really be part of algo?
      TermList qt = _algo.getSpecialVarTop(specVar);
      if(qt.isVar()) {
        return n->allChildren();
      } else {
        Node** match=n->childByTop(qt, false);
        if(match) {
          return pvi( 
            getConcatenatedIterator(
         getSingletonIterator(match),
         n->variableChildren() 
           ));
        } else {
          return n->variableChildren();
        }
      }
    }

    bool findNextLeaf()
    {
      CALL("SubstitutionTree::UnificationsIterator::findNextLeaf");

      if(_nodeIterators->isEmpty()) {
        //There are no node iterators in the stack, so there's nowhere
        //to look for the next leaf.
        //This shouldn't hapen during the regular retrieval process, but it
        //can happen when there are no literals inserted for a predicate,
        //or when predicates with zero arity are encountered.
        ASS(_bdStack->isEmpty());
        return false;
      }

      if(_inLeaf) {
        ASS(!_clientBDRecording);
        //Leave the current leaf
        _bdStack->pop().backtrack();
        _inLeaf=false;
      }

      ASS(!_clientBDRecording);
      ASS(_bdStack->length()+1==_nodeIterators->length());

      do {
        while(!_nodeIterators->top().hasNext() && !_bdStack->isEmpty()) {
          //backtrack undos everything that enter(...) method has done,
          //so it also pops one item out of the nodeIterators stack
          _bdStack->pop().backtrack();
          _svStack->pop();
        }
        if(!_nodeIterators->top().hasNext()) {
          return false;
        }
        Node* n=*_nodeIterators->top().next();

        BacktrackData bd;
        bool success=enter(n,bd);
        if(!success) {
          bd.backtrack();
          continue;
        } else {
          _bdStack->push(bd);
        }
      } while(!_inLeaf);
      return true;
    }

    bool enter(Node* n, BacktrackData& bd)
    {
      CALL("SubstitutionTree::UnificationsIterator::enter");

      bool success=true;
      bool recording=false;
      if(!n->term.isEmpty()) {
        //n is proper node, not a root

        recording=true;
        _algo.bdRecord(bd);
        success = _algo.associate(_svStack->top(),n->term,bd);
      }
      if(success) {
        if(n->isLeaf()) {
          _ldIterator=static_cast<Leaf*>(n)->allChildren();
          _inLeaf=true;
        } else {
          IntermediateNode* inode=static_cast<IntermediateNode*>(n);
          _svStack->push(inode->childVar);
          _nodeIterators->backtrackablePush(getNodeIterator(inode), bd);
        }
      }
      if(recording) {
        _algo.bdDone();
      }
      return success;
    }


    UnificationAlgorithm _algo;
    Recycled<VarStack> _svStack;
    bool _literalRetrieval;
    bool _retrieveSubstitution;
    bool _inLeaf;
    LDIterator _ldIterator;
    Recycled<Stack<NodeIterator>> _nodeIterators;
    Recycled<Stack<BacktrackData>> _bdStack;
    bool _clientBDRecording;
    BacktrackData _clientBacktrackData;
    IterCounter _parentIterCntr;
#if VDEBUG
    bool _tag;
#endif
  };


#if VDEBUG
public:
  static vstring nodeToString(Node* topNode);
  vstring toString() const;
  bool isEmpty() const;

  int _iteratorCnt;
#endif
  friend std::ostream& operator<<(std::ostream& out, SubstitutionTree const& self);

}; // class SubstiutionTree

template<> 
struct SubtitutionTreeConfig<Literal*> 
{
  static Literal* const& getKey(SubstitutionTree::LeafData const& ld)
  { return ld.literal;  }
};


template<> 
struct SubtitutionTreeConfig<TermList> 
{
  static TermList const& getKey(SubstitutionTree::LeafData const& ld)
  { return ld.term;  }
};



using RobUnificationsIterator = SubstitutionTree::UnificationsIterator<UnificationAlgorithms::RobUnification>;


} // namespace Indexing

#endif

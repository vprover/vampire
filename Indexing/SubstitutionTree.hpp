
/*
 * File SubstitutionTree.hpp.
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

#include "Kernel/RobSubstitution.hpp"
#include "Kernel/Renaming.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Sorts.hpp"
#include "Kernel/Signature.hpp"

#include "Lib/Allocator.hpp"

#include "Index.hpp"

#if VDEBUG

#include <iostream>
#include "Test/Output.hpp"

#endif

using namespace std;
using namespace Lib;
using namespace Kernel;

#define SUBST_CLASS RobSubstitution
//#define SUBST_CLASS EGSubstitution

#define UARR_INTERMEDIATE_NODE_MAX_SIZE 4

//SWITCHED OFF REORDERING FOR HIGHER ORDER DEVELOPMENT.
//ENSURE THAT SWITCH BACK ON ONCE UPDATED.
#define REORDERING 0

namespace Indexing {


/**
 * Class of substitution trees. In fact, contains an array of substitution
 * trees.
 * @since 16/08/2008 flight Sydney-San Francisco
 */
class SubstitutionTree
{
public:
  CLASS_NAME(SubstitutionTree);
  USE_ALLOCATOR(SubstitutionTree);

  SubstitutionTree(int nodes,bool useC=false, int hoVarNodes = 0);
  ~SubstitutionTree();

  // Tags are used as a debug tool to turn debugging on for a particular instance
  bool tag;
  virtual void markTagged(){ tag=true;}

//protected:

  struct LeafData {
    LeafData() {}
    LeafData(Clause* cls, Literal* literal, TermList term)
    : clause(cls), literal(literal), term(term), higherOrder(false){}
    LeafData(Clause* cls, Literal* literal)
    : clause(cls), literal(literal), higherOrder(false){ 
      term.makeEmpty(); 
    }

    inline
    bool operator==(const LeafData& o)
    { return clause==o.clause && literal==o.literal && term==o.term; }

    Clause* clause;
    Literal* literal;
    TermList term;
    bool higherOrder;
    //could this stack be the cause of out of memory error? AYB
    Stack<pair<unsigned, unsigned>> funcToFuncMap;  

    void insertFunctorPair(TermList* treeTerm, TermList* insertTerm){
      ASS(treeTerm->isTerm());
      ASS(insertTerm->isTerm());
      ASS(higherOrder);

      Term* t = treeTerm->term();
      Term* s = insertTerm->term();
      
      if(t->functor() != s->functor()){
        funcToFuncMap.push(make_pair(t->functor(), s->functor()));
      }
    } 
    /* 
    unsigned getFunctor(unsigned functor){
      ASS(higherOrder);
      unsigned res = 0;
      ALWAYS(funcToFuncMap.find(functor, res));
      return res;
    } */  

    vstring toString(){
      vstring ret = "LD " + literal->toString();// + " in " + clause->literalsOnlyToString();
      if(!term.isEmpty()){ ret += " with " +term.toString(); }
      return ret;
    }

  };
  
  
  typedef VirtualIterator<LeafData&> LDIterator;

  class LDComparator
  {
  public:
    inline
    static Comparison compare(const LeafData& ld1, const LeafData& ld2)
    {
      if(ld1.clause && ld2.clause && ld1.clause!=ld2.clause) {
        //if(ld1.clause->number()==ld2.clause->number()){
          //cout << "XXX " << ld1.clause << " and " << ld2.clause << endl;
          //cout << ld2.clause->toString() << endl;
        //}
        ASS_NEQ(ld1.clause->number(), ld2.clause->number());
        return (ld1.clause->number()<ld2.clause->number()) ? LESS : GREATER;
      }
      Comparison res;
      if(ld1.literal && ld2.literal && ld1.literal!=ld2.literal) {
        res=(ld1.literal->weight()>ld2.literal->weight())? LESS ://minimizing the non-determinism
          (ld1.literal->weight()<ld2.literal->weight())? GREATER :
          (ld1.literal<ld2.literal)? LESS : GREATER;
        ASS_NEQ(res, EQUAL);
      } else {
        ASS_EQ(ld1.clause,ld2.clause);
        ASS_EQ(ld1.literal,ld2.literal);
      //  if(ld1.term.isEmpty()) {
      //    ASS(ld2.term.isEmpty());
      //    res=EQUAL;
      //  } else {
      //    res=Term::lexicographicCompare(ld1.term,ld2.term);
      //  }
        res=(ld1.term<ld2.term)? LESS : (ld1.term>ld2.term)? GREATER : EQUAL;
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
    inline
    Node() { term.makeEmpty(); }
    inline
    Node(TermList ts) : term(ts) { }
    virtual ~Node();
    /** True if a leaf node */
    virtual bool isLeaf() const = 0;
    virtual bool isEmpty() const = 0;
    virtual bool withSorts(){ return false; }
    virtual bool hasEmptyHoData(){ return false; }
    /**
     * Return number of elements held in the node.
     *
     * Descendant classes should override this method.
     */
    virtual int size() const { NOT_IMPLEMENTED; }
    virtual NodeAlgorithm algorithm() const = 0;
    /*
     * This method should always be used when updating the term of a node.
     * In the case that the node contains higher-order data, using this method
     * will ensure that type data in the higher-order data will be updated.
     * By-passing the method could result in unsound proofs.
     */
    virtual void setTerm(TermList ts) = 0;

    /**
     * Remove all referenced structures without destroying them.
     *
     * This is used when the implementation of a node is being changed.
     * The current node will be deleted, but we don't want to destroy
     * structures, that are taken over by the new node implementation.
     */
    virtual void makeEmpty() { term.makeEmpty(); }
    static void split(Node** pnode, TermList* where, int var);
  
  /** Returns the type of the head symbol of term strored in the node.
    * The node must contain higher-order data before this method can
    * be called 
    */ 
    virtual OperatorType* getType() { NOT_IMPLEMENTED; }
#if VDEBUG
    virtual void assertValid() const {};
#endif

    /** term at this node */
    TermList term;

    virtual void print(unsigned depth=0){
       printDepth(depth);
       cout <<  "[" + term.toString() + "]" << endl;
    }
    void printDepth(unsigned depth){
      while(depth-->0){ cout <<" "; }
    }
  };


  typedef VirtualIterator<Node**> NodeIterator;
  typedef List<Node*> NodeList;
  class IntermediateNode;
    
  class ChildBySortHelper
  {
  public:
      
      CLASS_NAME(SubstitutionTree::ChildBySortHelper);
      USE_ALLOCATOR(ChildBySortHelper);
      
      ChildBySortHelper(IntermediateNode* p):  _parent(p)
      {
          bySort.ensure(Sorts::FIRST_USER_SORT);
          bySortTerms.ensure(Sorts::FIRST_USER_SORT);
      }
      
      /**
       * Return an iterator of child nodes whose top term has the same sort
       * as Termlist t. Only consider interpreted sorts.
       *
       */
      NodeIterator childBySort(TermList t)
      {
          CALL("SubstitutionTree::ChildBySortHelper::childBySort");
          unsigned srt;
          // only consider interpreted sorts
          if(SortHelper::tryGetResultSort(t,srt) && srt < Sorts::FIRST_USER_SORT && srt!=Sorts::SRT_DEFAULT){
              unsigned top = t.term()->functor();
              Stack<TermList>::Iterator fit(bySortTerms[srt]);
              auto withoutThisTop = getFilteredIterator(fit,NotTop(top));
              auto nodes = getMappingIterator(withoutThisTop,ByTopFn(this));
              return pvi(getFilteredIterator(nodes,NonzeroFn()));
          }
          return NodeIterator::getEmpty();
      }
      
      DArray<DHSet<unsigned>> bySort;
      DArray<Stack<TermList>> bySortTerms;
      
      IntermediateNode* _parent;
      /*
       * This is used for recording terms that might
       */
      void mightExistAsTop(TermList t)
      {
          CALL("SubstitutionTree::ChildBySortHelper::mightExistAsTop");
          if(!t.isTerm()){ return; }
          unsigned srt;
          if(SortHelper::tryGetResultSort(t,srt)){
              if(srt > Sorts::SRT_DEFAULT && srt < Sorts::FIRST_USER_SORT){
                  unsigned f = t.term()->functor();
                  if(bySort[srt].insert(f)){
                      bySortTerms[srt].push(t);
                  }
              }
          }
      }
      
  };// class SubstitutionTree::ChildBySortHelper
    
  class HoNode
  {
  public: 

      CLASS_NAME(SubstitutionTree::HoNode);
      USE_ALLOCATOR(HoNode);

      inline
      HoNode(TermList ts){
        //only if the term has a higher-order variable head does
        //it require a type stored.
        if(ts.isTerm() && ts.term()->hasVarHead()){
          termType = getFunctorType(ts.term());
        } else { 
          termType = 0;
        }
      }
      inline
      HoNode(OperatorType* type){
        termType = type;
      }

      virtual ~HoNode(){}

      inline void updateType(TermList ts){
        ASS(ts.isTerm() && ts.term()->hasVarHead())
        termType = getFunctorType(ts.term());
      }

      OperatorType* getType() { return termType; }

  protected:
      OperatorType* termType;
       
  };// HoNode

/*
  class LeafHoNode
      : public HoNode
  {
  public:

    CLASS_NAME(SubstitutionTree::LeafHoNode);
    USE_ALLOCATOR(LeafHoNode);

    inline
    LeafHoNode(TermList ts) : HoNode(ts){}

    ~LeafHoNode(){}
  }; //LeafHoNode*/


  class IntermediateHoNode 
      : public HoNode
  {
  public:
      
      inline
      IntermediateHoNode(TermList ts): HoNode(ts) {}
      inline
      IntermediateHoNode(OperatorType* type): HoNode(type) {}
      
     /* virtual ~IntermediateHoNode(){
        cout << "BASIC DESTRUCTOR CALLED" << endl;
      }*/
      
      void destroyChildren();
      void loadChildren(NodeIterator children);

      virtual NodeAlgorithm algorithm() const = 0;
      virtual Node** varHeadChildByType(TermList t, bool canCreate) = 0;
      virtual bool isEmpty() const = 0;
      virtual int size() const = 0;
      virtual NodeIterator allChildren() = 0;
      virtual void remove(TermList t) = 0;
      virtual void removeAllChildren() = 0;

      void makeEmpty()
      {
        removeAllChildren();
      }
  };// IntermediateHoNode

  class UArrIntermediateHoNode 
      : public IntermediateHoNode
  {
  public:
      
      CLASS_NAME(SubstitutionTree::UArrIntermediateHoNode);
      USE_ALLOCATOR(UArrIntermediateHoNode);
      
      inline
      UArrIntermediateHoNode(TermList ts): IntermediateHoNode(ts), _varHeadChildrenSize(0) {
        _hoVarNodes[0]=0;
      }

      ~UArrIntermediateHoNode()
      {
        if(!isEmpty()) {
          destroyChildren();
        }
      }

      NodeAlgorithm algorithm() const { return UNSORTED_LIST; }
      virtual Node** varHeadChildByType(TermList t, bool canCreate);
      virtual NodeIterator allChildren() {
        return pvi(PointerPtrIterator<Node*>(&_hoVarNodes[0],&_hoVarNodes[_varHeadChildrenSize]));
      }

      inline
      bool isEmpty() const { return  !_varHeadChildrenSize; }
      inline
      int size() const { return _varHeadChildrenSize; }

      virtual void remove(TermList t);
      virtual void removeAllChildren(){
        _varHeadChildrenSize=0;
        _hoVarNodes[0]=0;
      }

      void makeEmpty()
      {
        removeAllChildren();
      }

      int _varHeadChildrenSize;
      Node* _hoVarNodes[UARR_INTERMEDIATE_NODE_MAX_SIZE+1];
  };// UArrIntermediateHoNode

  class SListIntermediateHoNode 
      : public IntermediateHoNode
  {
  public:
      
      CLASS_NAME(SubstitutionTree::SListIntermediateHoNode);
      USE_ALLOCATOR(SListIntermediateHoNode);
      
      inline
      SListIntermediateHoNode(TermList ts):  IntermediateHoNode(ts) {}
      inline
      SListIntermediateHoNode(OperatorType* type):  IntermediateHoNode(type) {}


      virtual ~SListIntermediateHoNode()
      {
        if(!isEmpty()) {
          destroyChildren();
        }
      }

      void removeAllChildren()
      {
        while(!_hoVarNodes.isEmpty()) {
          _hoVarNodes.pop();
        }
      }

      static IntermediateHoNode* assimilate(IntermediateHoNode* orig);

      NodeAlgorithm algorithm() const { return SKIP_LIST; }
      virtual OperatorType* getType() { return termType; }
      inline
      bool isEmpty() const { return _hoVarNodes.isEmpty(); }
      inline
      int size() const { return _hoVarNodes.size(); }

      inline
      NodeIterator allChildren()
      {
        return pvi( HoNodeSkipList::PtrIterator(_hoVarNodes));
      }

      virtual Node** varHeadChildByType(TermList t, bool canCreate)
      {
        CALL("SubstitutionTree::SListIntermediateNode::childByTop");

        Node** res;
        bool found=_hoVarNodes.getPosition(t,res,canCreate);
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
        ASS(t.isTerm() && t.term()->hasVarHead());
        _hoVarNodes.remove(t);
      }

      void makeEmpty()
      {
        removeAllChildren();
      }


      class HoNodePtrComparator
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
          OperatorType* t1Type = getFunctorType(t1.term());
          OperatorType* t2Type = getFunctorType(t2.term());
          if(t1Type == t2Type){
            return EQUAL;
          }
          if(t1Type->arity() > t2Type->arity()){
            return GREATER;
          } else if (t1Type->arity() < t2Type->arity()) {
            return LESS;
          } else {
            for (unsigned i = 0; i > t1Type->arity(); i++) {
              if(t1Type->arg(i) > t2Type->arg(1)){
                return GREATER;
              } else if (t1Type->arg(i) < t2Type->arg(1)) {
                return LESS;
              }
            }
          }
          // if we reach here, both types are equal,
          // this should have been caught above.
          ASSERTION_VIOLATION;
        }

        static Comparison compare(Node* n1, Node* n2)
        { return compare(n1->term, n2->term); }
        static Comparison compare(TermList t1, Node* n2)
        { return compare(t1, n2->term); }
      };

      typedef SkipList<Node*,HoNodePtrComparator> HoNodeSkipList;
      HoNodeSkipList _hoVarNodes;
  };// HoNode


  class IntermediateNode
      : public Node
  {
  public:
    /** Build a new intermediate node which will serve as the root*/
    inline
    IntermediateNode(unsigned childVar) : childVar(childVar),_childBySortHelper(0), _hoData(0) {}

    /** Build a new intermediate node */
    inline
    IntermediateNode(TermList ts, unsigned childVar) : Node(ts), childVar(childVar),_childBySortHelper(0) {
      if(ts.isTerm() && ts.term()->hasVarHead()){
        _hoData = new UArrIntermediateHoNode(ts);
      } else {
        _hoData = 0;
      }
    }

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
     * If canCreate is false, null pointer is returned in case
     * suitable child does not exist.
     */
    virtual Node** childByTop(TermList t, bool canCreate) = 0;
    Node** varHeadChildByType(TermList t, bool canCreate){
      ASS(hasHigherOrderData());
      return _hoData->varHeadChildByType(t, canCreate);
    }
    inline
    OperatorType* getType() { 
      ASS(hasHigherOrderData());
      return _hoData->getType();
    }
    inline
    int hoDataSize(){
      if(hasHigherOrderData()){
        return _hoData->size();
      }
      return 0;
    }
    inline
    NodeAlgorithm hoDataAlgorithm(){
      if(hasHigherOrderData()){
        return _hoData->algorithm();
      }
      ASSERTION_VIOLATION;
    }
    inline
    bool hasEmptyHoData(){
      return hasHigherOrderData() && !hoDataSize();
    }
    inline void initialiseHoData(){
      _hoData = new UArrIntermediateHoNode(term);
    }
    inline 
    void setTerm(TermList ts){
      if(ts.isTerm() && ts.term()->hasVarHead()){
        if(!hasHigherOrderData()){
          _hoData = new UArrIntermediateHoNode(ts);
        } else {
          _hoData->updateType(ts);
        }
      } 
      term = ts;
    }

    inline bool hasHigherOrderData() const {return _hoData; }
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

    void makeEmpty()
    {
      Node::makeEmpty();
      removeAllChildren();
    }

    virtual NodeIterator childBySort(TermList t)
    {
        if(!_childBySortHelper) return NodeIterator::getEmpty();
        return _childBySortHelper->childBySort(t);
    }
    virtual void mightExistAsTop(TermList t) {
        if(_childBySortHelper){
          _childBySortHelper->mightExistAsTop(t);
        }
    }

    void loadChildren(NodeIterator children);

    const unsigned childVar;
    ChildBySortHelper* _childBySortHelper;
    IntermediateHoNode* _hoData;

    virtual void print(unsigned depth=0){
       auto children = allChildren();
       printDepth(depth);
       cout << "I [" << childVar << "] with " << term.toString() << endl;
       while(children.hasNext()){
         (*children.next())->print(depth+1);
       }
    }

  }; // class SubstitutionTree::IntermediateNode

    struct ByTopFn
    {
        ByTopFn(ChildBySortHelper* n) : node(n) {};
        DECL_RETURN_TYPE(Node**);
        OWN_RETURN_TYPE operator()(TermList t){
            return node->_parent->childByTop(t,false);
        }
    private:
        ChildBySortHelper* node;
    };
    struct NotTop
    {
        NotTop(unsigned t) : top(t) {};
        DECL_RETURN_TYPE(bool);
        OWN_RETURN_TYPE operator()(TermList t){
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
    {
      _hoData = 0;
    }
    /** Build a new leaf */
    inline
    Leaf(TermList ts) : Node(ts){
      if(ts.isTerm() && ts.term()->hasVarHead()){
        _hoData = new HoNode(ts);
      } else {
        _hoData = 0;
      }
    }

    inline 
    void setTerm(TermList ts){
      if(ts.isTerm() && ts.term()->hasVarHead()){
        if(!hasHigherOrderData()){
          _hoData = new HoNode(ts);
        } else {
          _hoData->updateType(ts);
        }
      } 
      term = ts;
    }

    inline
    bool isLeaf() const { return true; };
    virtual LDIterator allChildren() = 0;
    virtual void insert(LeafData ld) = 0;
    virtual void remove(LeafData ld) = 0;
    void loadChildren(LDIterator children);

    HoNode* _hoData; 
    inline bool hasHigherOrderData() const {return _hoData; }
    inline
    OperatorType* getType() { 
      ASS(hasHigherOrderData());
      return _hoData->getType();
    }

    virtual void print(unsigned depth=0){
       auto children = allChildren();
       while(children.hasNext()){
         printDepth(depth);
         cout << children.next().toString() << endl;
       } 
    }
  };

  //These classes and methods are defined in SubstitutionTree_Nodes.cpp
  class UListLeaf;
  class HoUListLeaf;
  class SListIntermediateNode;
  class SListLeaf;
  class HoSListLeaf;
  class SetLeaf;
  static Leaf* createLeaf();
  static Leaf* createLeaf(TermList ts);
  static void ensureLeafEfficiency(Leaf** l);
  inline
  static LeafData createLeafData(Clause* cls, Literal* lit, TermList t, bool ho = false){
    LeafData ld  = LeafData(cls, lit, t);
    if(ho){ld.higherOrder = true;} 
    return ld;   
  }
  static LeafData createLeafData(Clause* cls, Literal* lit, bool ho = false){
    LeafData ld  = LeafData(cls, lit);
    if(ho){ld.higherOrder = true;} 
    return ld;    
  }
  static IntermediateNode* createIntermediateNode(unsigned childVar,bool constraints);
  static IntermediateNode* createIntermediateNode(TermList ts, unsigned childVar,bool constraints);
  static void ensureIntermediateNodeEfficiency(IntermediateNode** inode);

  struct IsPtrToVarNodeFn
  {
    DECL_RETURN_TYPE(bool);
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
      if(hasHigherOrderData()){
        //cout << "and now deleting its ho data" << endl;
        //_hoData->destroyChildren();
        delete _hoData;
      }
    }

    virtual void removeAllChildren()
    {
      if(hasHigherOrderData()){
        _hoData->removeAllChildren();
      }
      _size=0;
      _nodes[0]=0;
    }

    NodeAlgorithm algorithm() const { return UNSORTED_LIST; }
    virtual bool isEmpty() const {
      if(hasHigherOrderData()){
        return !_hoData->size() && !_size;
      }
      return !_size; 
    }
    virtual int size() const {
      return _size; 
    }
    virtual NodeIterator allChildren()
    { 
      if(hasHigherOrderData()){
        return pvi(getConcatenatedIterator(PointerPtrIterator<Node*>(&_nodes[0],&_nodes[_size]),
                                           _hoData->allChildren()));
      }
      return pvi( PointerPtrIterator<Node*>(&_nodes[0],&_nodes[_size]) ); 
    }

    NodeIterator variableChildren()
    {
      return pvi( getFilteredIterator(PointerPtrIterator<Node*>(&_nodes[0],&_nodes[_size]),
        IsPtrToVarNodeFn()) );
    }
    virtual Node** childByTop(TermList t, bool canCreate);
    virtual void remove(TermList t);

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


  class UArrIntermediateNodeWithSorts
  : public UArrIntermediateNode
  {
  public:
   UArrIntermediateNodeWithSorts(unsigned childVar) : UArrIntermediateNode(childVar) {
     _childBySortHelper = new ChildBySortHelper(this);
   }
   UArrIntermediateNodeWithSorts(TermList ts, unsigned childVar) : UArrIntermediateNode(ts, childVar) {
     _childBySortHelper = new ChildBySortHelper(this);
   }
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
      if(hasHigherOrderData()){
        delete _hoData;
      }
    }

    void removeAllChildren()
    {
      if(hasHigherOrderData()){
        _hoData->removeAllChildren();
      }
      while(!_nodes.isEmpty()) {
        _nodes.pop();
      }
    }

    static IntermediateNode* assimilate(IntermediateNode* orig);

    inline
    NodeAlgorithm algorithm() const { return SKIP_LIST; }
    inline
    bool isEmpty() const { 
      if(hasHigherOrderData()){
        return _nodes.isEmpty() && _hoData->isEmpty();
      }
      return _nodes.isEmpty(); 
    }
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
      if(hasHigherOrderData()){
         return pvi(getConcatenatedIterator(NodeSkipList::PtrIterator(_nodes), _hoData->allChildren()));
      }
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
      if(t.isTerm() && t.term()->hasVarHead()){
        ASS(hasHigherOrderData());
        _hoData->remove(t);
        return;
      }
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

  class SListIntermediateNodeWithSorts
  : public SListIntermediateNode
  {
   public:
   SListIntermediateNodeWithSorts(unsigned childVar) : SListIntermediateNode(childVar) {
       _childBySortHelper = new ChildBySortHelper(this);
   }
   SListIntermediateNodeWithSorts(TermList ts, unsigned childVar) : SListIntermediateNode(ts, childVar) {
       _childBySortHelper = new ChildBySortHelper(this);
   }
  };

  class Binding {
  public:
    /** Number of the variable at this node */
    unsigned var;
    /** term at this node */
    TermList term;
    /** Create new binding */
    Binding(int v,TermList t) : var(v), term(t) {}
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

  typedef DHMap<unsigned,TermList,IdentityHash> BindingMap;
  //Using BinaryHeap as a BindingQueue leads to about 30% faster insertion,
  //that when SkipList is used.
  typedef BinaryHeap<Binding,Binding::Comparator> BindingQueue;
  //typedef SkipList<Binding,Binding::Comparator> BindingQueue;
//  typedef SkipList<unsigned,SpecVarComparator> SpecVarQueue;
  typedef BinaryHeap<unsigned,SpecVarComparator> SpecVarQueue;
  typedef Stack<unsigned> VarStack;

  inline
  static OperatorType* getFunctorType(const Term* t){
    if(t->hasVarHead()){
      return env.signature->getVarType(t->functor());
    }
    return env.signature->getFunction(t->functor())->fnType();
  }

  inline
  unsigned headSymbolSort(Term* t){
    return env.signature->getFunctorSort(t->functor());
  }
  void getBindings(Term* t, BindingMap& binding);

  Leaf* findLeaf(Node* root, BindingMap& svBindings);

  enum Mode{
    NORMAL_TERM = 0,
    VAR_HEAD_TERM = 1
  };

  void insert(Node** node,BindingMap& binding,LeafData ld, Term* initialTerm = NULL, Mode mode = NORMAL_TERM);
  void remove(Node** node,BindingMap& binding,LeafData ld);

  /** Number of the next variable */
  int _nextVar;
  /** Array of nodes */
  ZIArray<Node*> _nodes;
  /**  Array to terms that have variable heads */
  ZIArray<Node*> _hoVarNodes;
  /** enable searching with constraints for this tree */
  bool _useC;

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

  typedef pair<pair<LeafData*, ResultSubstitutionSP>,UnificationConstraintStackSP> QueryResult;


  class GenMatcher;

  /**
   * Iterator, that yields generalizations of given term/literal.
   */
  class FastGeneralizationsIterator
  : public IteratorCore<QueryResult>
  {
  public:
    FastGeneralizationsIterator(SubstitutionTree* parent, Node* root, Term* query,
            bool retrieveSubstitution, bool reversed,bool withoutTop,bool useC);

    ~FastGeneralizationsIterator();

    QueryResult next();
    bool hasNext();
  protected:
    void createInitialBindings(Term* t);
    void createReversedInitialBindings(Term* t);

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
      bool retrieveSubstitution, bool reversed, bool withoutTop, bool useC);
    ~FastInstancesIterator();

    bool hasNext();
    QueryResult next();
  protected:
    void createInitialBindings(Term* t);
    void createReversedInitialBindings(Term* t);
    bool findNextLeaf();

    bool enterNode(Node*& node);

  private:
    bool _literalRetrieval;
    bool _retrieveSubstitution;
    bool _inLeaf;
    LDIterator _ldIterator;

    InstMatcher* _subst;

    Renaming _resultDenormalizer;
    SubstitutionTree* _tree;
    Node* _root;

    Stack<void*> _alternatives;
    Stack<unsigned> _specVarNumbers;
    Stack<NodeAlgorithm> _nodeTypes;
  };

  class UnificationsIterator
  : public IteratorCore<QueryResult>
  {
  public:
    UnificationsIterator(SubstitutionTree* parent, Node* root, Term* query, bool retrieveSubstitution, bool reversed,bool withoutTop, bool useC);
    ~UnificationsIterator();

    bool hasNext();
    QueryResult next();
    bool tag;
  protected:
    virtual bool associate(TermList query, TermList node, BacktrackData& bd);
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

    SUBST_CLASS subst;
    VarStack svStack;

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
    SubstitutionTree* tree;
    bool useConstraints;
    Stack<UnificationConstraint> constraints;
  };

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

}; // class SubstiutionTree

} // namespace Indexing

#endif

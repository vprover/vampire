/**
 * @file SubstitutionTree_Nodes.cpp
 * Different SubstitutionTree Node implementations.
 */

#include "../Lib/VirtualIterator.hpp"
#include "../Lib/List.hpp"
#include "../Lib/SkipList.hpp"
#include "../Lib/DHMultiset.hpp"

#include "Index.hpp"
#include "SubstitutionTree.hpp"

using namespace Indexing;

class SubstitutionTree::IsPtrToVarNodePredicate
{
public:
  static bool eval(Node** n)
  {
    return (*n)->term.isVar();
  }
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

class SubstitutionTree::UListIntermediateNode
: public SubstitutionTree::IntermediateNode
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

class SubstitutionTree::UListLeaf
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


class SubstitutionTree::SListIntermediateNode
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


class SubstitutionTree::SListLeaf
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

class SubstitutionTree::SetLeaf
: public SubstitutionTree::Leaf
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


SubstitutionTree::Leaf* SubstitutionTree::createLeaf()
{
  return new UListLeaf(); 
}

SubstitutionTree::Leaf* SubstitutionTree::createLeaf(TermList* ts)
{
  return new UListLeaf(ts);
}

SubstitutionTree::IntermediateNode* SubstitutionTree::createIntermediateNode()
{
  return new UListIntermediateNode();
}

SubstitutionTree::IntermediateNode* SubstitutionTree::createIntermediateNode(TermList* ts)
{
  return new UListIntermediateNode(ts);
}

SubstitutionTree::Node** SubstitutionTree::UListIntermediateNode::
	childByTop(TermList* t, bool canCreate)
{
  CALL("SubstitutionTree::UListIntermediateNode::childByTop");
  
  NodeList** nl=&_nodes;
  while(*nl && !sameTop(t, &(*nl)->head()->term)) {
	nl=reinterpret_cast<NodeList**>(&(*nl)->tailReference());
  }
  if(!*nl && canCreate) {
  	*nl=new NodeList(0,0);
  	_size++;
  }
  if(*nl) {
	return (*nl)->headPtr(); 
  } else {
	return 0;
  }
}

void SubstitutionTree::UListIntermediateNode::remove(TermList* t)
{
  CALL("SubstitutionTree::UListIntermediateNode::remove");
  
  NodeList** nl=&_nodes;
  while(!sameTop(t, &(*nl)->head()->term)) {
	nl=reinterpret_cast<NodeList**>(&(*nl)->tailReference());
	ASS(*nl);
  }
  NodeList* removedPiece=*nl;
  *nl=static_cast<NodeList*>((*nl)->tail());
  delete removedPiece;
  _size--;
}

/**
 * Take an IntermediateNode, destroy it, and return 
 * SListIntermediateNode with the same content.
 */
SubstitutionTree::SListIntermediateNode* SubstitutionTree::SListIntermediateNode
	::assimilate(IntermediateNode* orig) 
{
  SListIntermediateNode* res=new SListIntermediateNode(&orig->term);
  res->loadChildren(orig->allChildren()); 
  orig->term.makeEmpty();
  delete orig;
  return res;
}

/**
 * Take a Leaf, destroy it, and return SListLeaf 
 * with the same content.
 */
SubstitutionTree::SListLeaf* SubstitutionTree::SListLeaf::assimilate(Leaf* orig) 
{
  SListLeaf* res=new SListLeaf(&orig->term);
  res->loadClauses(orig->allCaluses()); 
  orig->term.makeEmpty();
  delete orig;
  return res;
}

/**
 * Take a Leaf, destroy it, and return SetLeaf 
 * with the same content.
 */
SubstitutionTree::SetLeaf* SubstitutionTree::SetLeaf::assimilate(Leaf* orig) 
{
  SetLeaf* res=new SetLeaf(&orig->term);
  res->loadClauses(orig->allCaluses()); 
  orig->term.makeEmpty();
  delete orig;
  return res;
}


void SubstitutionTree::ensureLeafEfficiency(Leaf** leaf)
{
  CALL("SubstitutionTree::ensureLeafEfficiency");

  if( (*leaf)->algorithm()==UNSORTED_LIST && (*leaf)->size()>5 ) {
    //*leaf=SListLeaf::assimilate(*leaf);
    *leaf=SetLeaf::assimilate(*leaf);
  }
}

void SubstitutionTree::ensureIntermediateNodeEfficiency(IntermediateNode** inode)
{
  CALL("SubstitutionTree::ensureIntermediateNodeEfficiency");

  if( (*inode)->algorithm()==UNSORTED_LIST && (*inode)->size()>3 ) {
    *inode=SListIntermediateNode::assimilate(*inode);
  }
}

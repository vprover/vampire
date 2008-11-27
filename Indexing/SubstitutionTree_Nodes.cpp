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
  UListLeaf() : _children(0), _size(0) {}
  inline
  UListLeaf(const TermList* ts) : Leaf(ts), _children(0), _size(0) {}
  ~UListLeaf()
  {
    if(_children) {
      _children->destroy();
    }
  }

  inline
  NodeAlgorithm algorithm() const { return UNSORTED_LIST; }
  inline
  bool isEmpty() const { return !_children; }
  inline
  int size() const { return _size; }
  inline
  LDIterator allChildren()
  {
    return LDIterator(new ProxyIterator<LeafData,LDList::Iterator>(
	    LDList::Iterator(_children)));
  }
  inline
  void insert(LeafData ld)
  {
    _children=new LDList(ld, _children);
    _size++;
  }
  inline
  void remove(LeafData ld)
  {
    _children=_children->remove(ld);
    _size--;
  }
private:
  typedef List<LeafData> LDList;
  LDList* _children;
  int _size;
};


class SubstitutionTree::SListIntermediateNode
: public IntermediateNode
{
public:
  SListIntermediateNode() {}
  SListIntermediateNode(const TermList* ts) : IntermediateNode(ts) {}
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
      CALL("SubstitutionTree::SListIntermediateNode::NodePtrComparator::compare");

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
  bool isEmpty() const { return _children.isEmpty(); }
#if VDEBUG
  inline
  int size() const { return _children.size(); }
#endif
  inline
  LDIterator allChildren()
  {
    return LDIterator(new ProxyIterator<LeafData,LDSkipList::Iterator>(
	    LDSkipList::Iterator(_children)));
  }
  void insert(LeafData ld) { _children.insert(ld); }
  void remove(LeafData ld) { _children.remove(ld); }
private:
  class LDComparator
  {
  public:
    inline
    static Comparison compare(const LeafData& ld1, const LeafData& ld2)
    {
      return (ld1.clause<ld2.clause)? LESS :
      	(ld1.clause>ld2.clause)? GREATER :
      	(ld1.data<ld2.data)? LESS : (ld1.data==ld2.data) ? EQUAL : GREATER;
    }
  };
  typedef SkipList<LeafData,LDComparator> LDSkipList;
  LDSkipList _children;

  friend class SubstitutionTree;
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
  while(*nl && !TermList::sameTop(t, &(*nl)->head()->term)) {
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
  while(!TermList::sameTop(t, &(*nl)->head()->term)) {
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
  CALL("SubstitutionTree::SListIntermediateNode::assimilate");

  SListIntermediateNode* res=new SListIntermediateNode(&orig->term);
  res->loadChildren(orig->allChildren());
  orig->makeEmpty();
  delete orig;
  return res;
}

/**
 * Take a Leaf, destroy it, and return SListLeaf
 * with the same content.
 */
SubstitutionTree::SListLeaf* SubstitutionTree::SListLeaf::assimilate(Leaf* orig)
{
  CALL("SubstitutionTree::SListLeaf::assimilate");

  SListLeaf* res=new SListLeaf(&orig->term);
  res->loadChildren(orig->allChildren());
  orig->makeEmpty();
  delete orig;
  return res;
}

void SubstitutionTree::ensureLeafEfficiency(Leaf** leaf)
{
  CALL("SubstitutionTree::ensureLeafEfficiency");

  if( (*leaf)->algorithm()==UNSORTED_LIST && (*leaf)->size()>5 ) {
    *leaf=SListLeaf::assimilate(*leaf);
  }
}

void SubstitutionTree::ensureIntermediateNodeEfficiency(IntermediateNode** inode)
{
  CALL("SubstitutionTree::ensureIntermediateNodeEfficiency");

  if( (*inode)->algorithm()==UNSORTED_LIST && (*inode)->size()>3 ) {
    *inode=SListIntermediateNode::assimilate(*inode);
  }
}

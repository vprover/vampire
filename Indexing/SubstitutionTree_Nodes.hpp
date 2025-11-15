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
 * @file SubstitutionTree_Nodes.hpp
 * Different SubstitutionTree Node implementations.
 */


#include "Lib/DHMultiset.hpp"
#include "Lib/Exception.hpp"
#include "Lib/List.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/SkipList.hpp"
#include "Lib/VirtualIterator.hpp"
#include "Lib/Environment.hpp"

#include "Shell/Options.hpp"

#include "Index.hpp"
#include "SubstitutionTree.hpp"


namespace Indexing
{

template<class LeafData_>
class SubstitutionTree<LeafData_>::UListLeaf
: public Leaf
{
public:
  inline
  UListLeaf() : _children(0), _size(0) {}
  inline
  UListLeaf(TermList ts) : Leaf(ts), _children(0), _size(0) {}
  ~UListLeaf() override
  {
    LDList::destroy(_children);
  }

  inline
  NodeAlgorithm algorithm() const final { return UNSORTED_LIST; }
  inline
  bool isEmpty() const final { return !_children; }
  inline
  int size() const final { return _size; }
  inline
  LDIterator allChildren() final
  {
    return pvi( iterTraits(typename LDList::RefIterator(_children)).map([](auto& x) { return &x; }) );
  }
  inline
  void insert(LeafData ld) final
  {
    LDList::push(ld, _children);
    _size++;
  }
  inline
  void remove(LeafData ld) final
  {
    _children = LDList::remove(ld, _children);
    _size--;
  }

  USE_ALLOCATOR(UListLeaf);
private:
  typedef List<LeafData> LDList;
  LDList* _children;
  int _size;
};


template<class LeafData_>
class SubstitutionTree<LeafData_>::SListLeaf
: public Leaf
{
public:
  SListLeaf() {}
  SListLeaf(TermList ts) : Leaf(ts) {}

  static SListLeaf* assimilate(Leaf* orig);

  inline
  NodeAlgorithm algorithm() const final { return SKIP_LIST; }
  inline
  bool isEmpty() const final { return _children.isEmpty(); }
  inline
  int size() const final { return _children.size(); }
  inline
  LDIterator allChildren() final
  {
    return pvi( iterTraits(typename LDSkipList::RefIterator(_children)).map([](auto& x) { return &x; }) );
  }
  void insert(LeafData ld) override { _children.insert(ld); }
  void remove(LeafData ld) override { _children.remove(ld); }

  USE_ALLOCATOR(SListLeaf);
private:
  typedef SkipList<LeafData,LDComparator> LDSkipList;
  LDSkipList _children;

  friend class SubstitutionTree;
};


template<class LeafData_>
typename SubstitutionTree<LeafData_>::Leaf* SubstitutionTree<LeafData_>::createLeaf()
{
  return new UListLeaf();
}

template<class LeafData_>
typename SubstitutionTree<LeafData_>::Leaf* SubstitutionTree<LeafData_>::createLeaf(TermList ts)
{
  return new UListLeaf(ts);
}

template<class LeafData_>
typename SubstitutionTree<LeafData_>::IntermediateNode* SubstitutionTree<LeafData_>::createIntermediateNode(unsigned childVar)
{
  return new UArrIntermediateNode(childVar);
}

template<class LeafData_>
typename SubstitutionTree<LeafData_>::IntermediateNode* SubstitutionTree<LeafData_>::createIntermediateNode(TermList ts, unsigned childVar)
{
  return new UArrIntermediateNode(ts, childVar);
}

template<class LeafData_>
void SubstitutionTree<LeafData_>::IntermediateNode::destroyChildren()
{
  static Stack<Node*> toDelete;
  toDelete.reset();
  toDelete.push(this);
  while(toDelete.isNonEmpty()) {
    Node* n=toDelete.pop();
    if(!n->isLeaf()) {
      IntermediateNode* in=static_cast<IntermediateNode*>(n);
      NodeIterator children=in->allChildren();
      while(children.hasNext()) {
	toDelete.push(*children.next());
      }
      in->removeAllChildren();
    }
    if(n!=this) {
      delete n;
    }
  }
}

template<class LeafData_>
typename SubstitutionTree<LeafData_>::Node** SubstitutionTree<LeafData_>::UArrIntermediateNode::
	childByTop(TermList::Top t, bool canCreate)
{
  for(int i=0;i<_size;i++) {
    if(t == _nodes[i]->top()) {
      return &_nodes[i];
    }
  }
  if(canCreate) {
    ASS_L(_size,UARR_INTERMEDIATE_NODE_MAX_SIZE);
    ASS_EQ(_nodes[_size],0);
    _nodes[++_size]=0;
    return &_nodes[_size-1];
  }
  return 0;
}

template<class LeafData_>
void SubstitutionTree<LeafData_>::UArrIntermediateNode::remove(TermList::Top t)
{
  for(int i=0;i<_size;i++) {
    if(t == _nodes[i]->top()) {
      _size--;
      _nodes[i]=_nodes[_size];
      _nodes[_size]=0;
      return;
    }
  }
  ASSERTION_VIOLATION;
}

/**
 * Take an IntermediateNode, destroy it, and return
 * SListIntermediateNode with the same content.
 */
template<class LeafData_>
typename SubstitutionTree<LeafData_>::IntermediateNode* SubstitutionTree<LeafData_>::SListIntermediateNode
	::assimilate(IntermediateNode* orig)
{
  IntermediateNode* res= 0;
  // TODO refactor such that children are not copied here, and deleted at (2), but moved instead
  res = new SListIntermediateNode(orig->term(), orig->childVar);
  res->loadChildren(orig->allChildren());
  orig->makeEmpty();
  // TODO (2) see above
  delete orig;
  return res;
}

/**
 * Take a Leaf, destroy it, and return SListLeaf
 * with the same content.
 */
template<class LeafData_>
typename SubstitutionTree<LeafData_>::SListLeaf* SubstitutionTree<LeafData_>::SListLeaf::assimilate(Leaf* orig)
{
  SListLeaf* res=new SListLeaf(orig->term());
  res->loadChildren(orig->allChildren());
  orig->makeEmpty();
  delete orig;
  return res;
}

template<class LeafData_>
void SubstitutionTree<LeafData_>::ensureLeafEfficiency(Leaf** leaf)
{
  if( (*leaf)->algorithm()==UNSORTED_LIST && (*leaf)->size()>5 ) {
    *leaf=SListLeaf::assimilate(*leaf);
  }
}

template<class LeafData_>
void SubstitutionTree<LeafData_>::ensureIntermediateNodeEfficiency(IntermediateNode** inode)
{
  if( (*inode)->algorithm()==UNSORTED_LIST && (*inode)->size()>3 ) {
    *inode=SListIntermediateNode::assimilate(*inode);
  }
}

} // namespace Indexing


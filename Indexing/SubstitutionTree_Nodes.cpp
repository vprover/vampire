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
 * @file SubstitutionTree_Nodes.cpp
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
  ~UListLeaf()
  {
    LDList::destroy(_children);
  }

  inline
  NodeAlgorithm algorithm() const final override { return UNSORTED_LIST; }
  inline
  bool isEmpty() const final override { return !_children; }
  inline
  int size() const final override { return _size; }
  inline
  LDIterator allChildren() const final override
  {
    return pvi( typename LDList::RefIterator(_children) );
  }
  inline
  void insert(LeafData ld) final override
  {
    CALL("SubstitutionTree::UListLeaf::insert");
    LDList::push(ld, _children);
    _size++;
  }
  inline
  void remove(LeafData ld) final override
  {
    CALL("SubstitutionTree::UListLeaf::remove");
    _children = LDList::remove(ld, _children);
    _size--;
  }

  CLASS_NAME(SubstitutionTree::UListLeaf);
  USE_ALLOCATOR(UListLeaf);
#if VDEBUG 
  void assertValid() const final override {}
#endif
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
  NodeAlgorithm algorithm() const final override { return SKIP_LIST; }
  inline
  bool isEmpty() const final override { return _children.isEmpty(); }
  inline
  int size() const final override { return _children.size(); }
  inline
  LDIterator allChildren() const final override
  {
    return pvi( typename LDSkipList::RefIterator(_children) );
  }
  void insert(LeafData ld) final override
  {
    CALL("SubstitutionTree::SListLeaf::insert");
    _children.insert(ld);
  }
  void remove(LeafData ld) final override
  {
    CALL("SubstitutionTree::SListLeaf::remove");
    _children.remove(ld);
  }

  CLASS_NAME(SubstitutionTree::SListLeaf);
  USE_ALLOCATOR(SListLeaf);
#if VDEBUG 
  void assertValid() const final override {}
#endif
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
  CALL("SubstitutionTree::createIntermediateNode/2");
  return new UArrIntermediateNode(childVar);
}

template<class LeafData_>
typename SubstitutionTree<LeafData_>::IntermediateNode* SubstitutionTree<LeafData_>::createIntermediateNode(TermList ts, unsigned childVar)
{
  CALL("SubstitutionTree::createIntermediateNode/3");
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
	childByTop(TermList t, bool canCreate)
{
  CALL("SubstitutionTree::UArrIntermediateNode::childByTop");

  for(int i=0;i<_size;i++) {
    if(TermList::sameTop(t, _nodes[i]->term)) {
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
void SubstitutionTree<LeafData_>::UArrIntermediateNode::remove(TermList t)
{
  CALL("SubstitutionTree::UArrIntermediateNode::remove");

  for(int i=0;i<_size;i++) {
    if(TermList::sameTop(t, _nodes[i]->term)) {
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
  CALL("SubstitutionTree::SListIntermediateNode::assimilate");

  IntermediateNode* res = new SListIntermediateNode(orig->term, orig->childVar);
  res->loadChildren(orig->allChildren());
  orig->makeEmpty();
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
  CALL("SubstitutionTree::SListLeaf::assimilate");

  SListLeaf* res=new SListLeaf(orig->term);
  res->loadChildren(orig->allChildren());
  orig->makeEmpty();
  delete orig;
  return res;
}

template<class LeafData_>
void SubstitutionTree<LeafData_>::ensureLeafEfficiency(Leaf** leaf)
{
  CALL("SubstitutionTree::ensureLeafEfficiency");

  if( (*leaf)->algorithm()==UNSORTED_LIST && (*leaf)->size()>5 ) {
    *leaf=SListLeaf::assimilate(*leaf);
  }
}

template<class LeafData_>
void SubstitutionTree<LeafData_>::ensureIntermediateNodeEfficiency(IntermediateNode** inode)
{
  CALL("SubstitutionTree::ensureIntermediateNodeEfficiency");

  if( (*inode)->algorithm()==UNSORTED_LIST && (*inode)->size()>3 ) {
    *inode=SListIntermediateNode::assimilate(*inode);
  }
}

} // namespace Indexing


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

class SubstitutionTree::UListLeaf
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
  NodeAlgorithm algorithm() const { return UNSORTED_LIST; }
  inline
  bool isEmpty() const { return !_children; }
  inline
  int size() const { return _size; }
  inline
  LDIterator allChildren()
  {
    return pvi( LDList::RefIterator(_children) );
  }
  inline
  void insert(LeafData ld)
  {
    CALL("SubstitutionTree::UListLeaf::insert");
    LDList::push(ld, _children);
    _size++;
  }
  inline
  void remove(LeafData ld)
  {
    CALL("SubstitutionTree::UListLeaf::remove");
    _children = LDList::remove(ld, _children);
    _size--;
  }

  CLASS_NAME(SubstitutionTree::UListLeaf);
  USE_ALLOCATOR(UListLeaf);
private:
  typedef List<LeafData> LDList;
  LDList* _children;
  int _size;
};


class SubstitutionTree::SListLeaf
: public Leaf
{
public:
  SListLeaf() {}
  SListLeaf(TermList ts) : Leaf(ts) {}

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
    return pvi( LDSkipList::RefIterator(_children) );
  }
  void insert(LeafData ld) {
    CALL("SubstitutionTree::SListLeaf::insert");
    _children.insert(ld);
  }
  void remove(LeafData ld) {
    CALL("SubstitutionTree::SListLeaf::remove");
    _children.remove(ld);
  }

  CLASS_NAME(SubstitutionTree::SListLeaf);
  USE_ALLOCATOR(SListLeaf);
private:
  typedef SkipList<LeafData,LDComparator> LDSkipList;
  LDSkipList _children;

  friend class SubstitutionTree;
};


SubstitutionTree::Leaf* SubstitutionTree::createLeaf()
{
  return new UListLeaf();
}

SubstitutionTree::Leaf* SubstitutionTree::createLeaf(TermList ts)
{
  return new UListLeaf(ts);
}

SubstitutionTree::IntermediateNode* SubstitutionTree::createIntermediateNode(unsigned childVar,bool useC)
{
  CALL("SubstitutionTree::createIntermediateNode/2");
  if(useC){ return new UArrIntermediateNodeWithSorts(childVar); }
  return new UArrIntermediateNode(childVar);
}

SubstitutionTree::IntermediateNode* SubstitutionTree::createIntermediateNode(TermList ts, unsigned childVar,bool useC)
{
  CALL("SubstitutionTree::createIntermediateNode/3");
  if(useC){ return new UArrIntermediateNodeWithSorts(ts, childVar); }
  return new UArrIntermediateNode(ts, childVar);
}

void SubstitutionTree::IntermediateNode::destroyChildren()
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

SubstitutionTree::Node** SubstitutionTree::UArrIntermediateNode::
	childByTop(TermList t, bool canCreate)
{
  CALL("SubstitutionTree::UArrIntermediateNode::childByTop");

  for(int i=0;i<_size;i++) {
    if(TermList::sameTop(t, _nodes[i]->term)) {
      return &_nodes[i];
    }
  }
  if(canCreate) {
    mightExistAsTop(t);
    ASS_L(_size,UARR_INTERMEDIATE_NODE_MAX_SIZE);
    ASS_EQ(_nodes[_size],0);
    _nodes[++_size]=0;
    return &_nodes[_size-1];
  }
  return 0;
}

void SubstitutionTree::UArrIntermediateNode::remove(TermList t)
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
SubstitutionTree::IntermediateNode* SubstitutionTree::SListIntermediateNode
	::assimilate(IntermediateNode* orig)
{
  CALL("SubstitutionTree::SListIntermediateNode::assimilate");

  IntermediateNode* res= 0;
  if(orig->withSorts()){
    res = new SListIntermediateNodeWithSorts(orig->term, orig->childVar);
    res->_childBySortHelper->loadFrom(orig->_childBySortHelper);
  }else{
    res = new SListIntermediateNode(orig->term, orig->childVar);
  }
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

  SListLeaf* res=new SListLeaf(orig->term);
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

}

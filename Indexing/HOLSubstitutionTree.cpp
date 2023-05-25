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
 * @file TermSubstitutionTree.cpp
 * Implements class TermSubstitutionTree.
 */

#if VHOL

#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Kernel/Term.hpp"
#include "Indexing/HOLSubstitutionTree.hpp"

namespace Indexing
{

using namespace Lib;
using namespace Kernel;


using Subterm = HOLSubstitutionTree::Subterm;

std::ostream& operator<< (ostream& out, const Subterm& t )
{
  return out<<t.term().toString() << " | splittable : " << t.splittable();
}

struct HOLUnresolvedSplitRecord
{
  HOLUnresolvedSplitRecord() {}
  HOLUnresolvedSplitRecord(unsigned var, TermList original, bool splittable)
  : var(var), original(original), splittable(splittable) {}

  unsigned var;
  TermList original;
  bool splittable;
};

class HOLBinding {
public:
  /** Number of the variable at this node */
  unsigned var;
  /** term at this node */
  Subterm term;
  /** Create new binding */
  HOLBinding(int v, Subterm t) : var(v), term(t) {}
};

struct HOLBindingComparator
{
  static Comparison compare(const HOLUnresolvedSplitRecord& r1, const HOLUnresolvedSplitRecord& r2)
  {
    bool r1HasSpecVars=r1.original.isTerm() && !r1.original.term()->shared();
    bool r2HasSpecVars=r2.original.isTerm() && !r2.original.term()->shared();
    if( r1HasSpecVars && !r2HasSpecVars ) {
      return GREATER;
    }
    if( r2HasSpecVars && !r1HasSpecVars ) {
      return LESS;
    }
    return Int::compare(r2.var,r1.var);
  }
  static Comparison compare(const HOLBinding& b1, const HOLBinding& b2)
  {
#if REORDERING
    return Int::compare(b2.var,b1.var);
#else
    return Int::compare(b1.var,b2.var);
#endif
  }
};


void HOLSubstitutionTree::higherOrderInsert(HOLBindingMap& svBindings,LeafData ld)
{
#define DEBUG_INSERT(...)  //DBG(__VA_ARGS__)
  CALL("SubstitutionTree::splittableInsert");
  ASS_EQ(_iterCnt,0);

  auto pnode = &_root;
  DEBUG_INSERT("insert: ", svBindings, " into ", *this)

  if(*pnode == 0) {
    if (svBindings.isEmpty()) {
      auto leaf = createLeaf();
      leaf->insert(std::move(ld));
      *pnode = leaf;
      DEBUG_INSERT(0, "out: ", *this);
      return;
    } else {
      // create root
      *pnode=createIntermediateNode(svBindings.getOneKey());
    }
  }
  if(svBindings.isEmpty()) {
    ASS((*pnode)->isLeaf());
    ensureLeafEfficiency(reinterpret_cast<Leaf**>(pnode));
    static_cast<Leaf*>(*pnode)->insert(ld);
    DEBUG_INSERT("out: ", *this);
    return;
  }

  typedef BinaryHeap<HOLUnresolvedSplitRecord, HOLBindingComparator> SplitRecordHeap;
  static SplitRecordHeap unresolvedSplits;
  unresolvedSplits.reset();

  ASS((*pnode));
  ASS(!(*pnode)->isLeaf());

start:

#if REORDERING
  ASS(!(*pnode)->isLeaf() || !unresolvedSplits.isEmpty());
  bool canPostponeSplits=false;
  if((*pnode)->isLeaf() || (*pnode)->algorithm()!=UNSORTED_LIST) {
    canPostponeSplits=false;
  } else {
    UArrIntermediateNode* inode = static_cast<UArrIntermediateNode*>(*pnode);
    canPostponeSplits = inode->size()==1;
    if(canPostponeSplits) {
      unsigned boundVar=inode->childVar;
      Node* child=inode->_nodes[0];
      bool removeProblematicNode=false;
      if(svBindings.find(boundVar)) {
        Subterm term=svBindings.get(boundVar);

        bool wouldDescendIntoChild = inode->childByTop(term.top(),false)!=0;
        ASS_EQ(wouldDescendIntoChild, term.top() == child->top());
        if(!wouldDescendIntoChild) {
          //if we'd have to perform all postponed splitting due to
          //node with a single child, we rather remove that node
          //from the tree and deal with the binding, it represented,
          //later.
          removeProblematicNode=true;
        }
      } else if(!child->term.isTerm() || child->term.term()->shared()) {
        //We can remove nodes binding to special variables undefined in our branch
        //of the tree, as long as we're sure, that during split resolving we put these
        //binding nodes below nodes that define spec. variables they bind.
        removeProblematicNode=true;
      } else {
        canPostponeSplits = false;
      }
      if(removeProblematicNode) {
        unresolvedSplits.insert(HOLUnresolvedSplitRecord(inode->childVar, child->term, child->splittable()));
        child->term=inode->term;
        child->setSplittable(inode->splittable()); //TODO is this correct???
        *pnode=child;
        inode->makeEmpty();
        delete inode;
        goto start;
      }
    }
  }
  canPostponeSplits|=unresolvedSplits.isEmpty();
  if(!canPostponeSplits) {

    while(!unresolvedSplits.isEmpty()) {
      HOLUnresolvedSplitRecord urr=unresolvedSplits.pop();

      Node* node=*pnode;
      IntermediateNode* newNode = createIntermediateNode(node->term, urr.var, node->splittable());

      node->term=urr.original;
      node->setSplittable(urr.splittable);

      *pnode=newNode;

      Node** nodePosition=newNode->childByTop(node->top(), true);
      ASS(!*nodePosition);
      *nodePosition=node;
    }
  }
#endif
  ASS(!(*pnode)->isLeaf());

  IntermediateNode* inode = static_cast<IntermediateNode*>(*pnode);
  ASS(inode);

  unsigned boundVar=inode->childVar;
  Subterm term=svBindings.get(boundVar);
  svBindings.remove(boundVar);

  //Into pparent we store the node, we might be inserting into.
  //So in the case we do insert, we might check whether this node
  //needs expansion.
  Node** pparent=pnode;
  pnode=inode->childByTop(term.top(),true);

  if (*pnode == 0) {
    HOLBindingMap::Iterator svit(svBindings);
    BinaryHeap<HOLBinding, HOLBindingComparator> remainingBindings;
    while (svit.hasNext()) {
      unsigned var;
      Subterm term;
      svit.next(var, term);
      remainingBindings.insert(HOLBinding(var, term));
    }
    while (!remainingBindings.isEmpty()) {
      HOLBinding b=remainingBindings.pop();
      IntermediateNode* inode = createIntermediateNode(term.term(), b.var, term.splittable());
      term=b.term;

      *pnode = inode;
      pnode = inode->childByTop(term.top(),true);
    }
    Leaf* lnode=createLeaf(term.term(), term.splittable());
    *pnode=lnode;
    lnode->insert(ld);

    ensureIntermediateNodeEfficiency(reinterpret_cast<IntermediateNode**>(pparent));
    DEBUG_INSERT("out: ", *this);
    return;
  }

  ASS(term.top() == (*pnode)->top());

  TermList* tt = term.termPtr();
  TermList* ss = &(*pnode)->term;

  // ss is the term in node, tt is the term to be inserted
  // ss and tt have the same top symbols but are not equal
  // create the common subterm of ss,tt and an alternative node
  Stack<SubtermPair> toProcess(64);
  toProcess.push(SubtermPair(ss, (*pnode)->splittable(), tt, term.splittable()));

  while(!toProcess.isEmpty()) {
    auto pair = toProcess.pop();

    TermList* lhs = pair.lhs();
    TermList* rhs = pair.rhs();

    // I am a bit concerned about doing
    // an == check on possibly non-shared terms,
    // but that is what existing code does
    if(*lhs == *rhs){
    } else if(!lhs->isVar() && !rhs->isVar() && pair.lhsTop() == pair.rhsTop()){
      // we can have two vars which are not == but have the same top
      // since the top() function does take into accoutn whether one variable is
      // special. Might be worth changing this TODO

      // same top different content
      ASS(!lhs->isVar()        && !rhs->isVar());
      ASS(!lhs->isLambdaTerm() && !rhs->isLambdaTerm());
      ASS_EQ(lhs->term()->functor(), rhs->term()->functor());

      if (lhs->isTerm() && lhs->term()->shared()) {
        Term* s = lhs->term();
        // create a shallow copy of s
        s = Term::cloneNonShared(s);
        lhs->setTerm(s);
      } 

      Term* l = lhs->term();
      Term* r = rhs->term();           

      if(rhs->isApplication()){
        ASS(lhs->isApplication());
        toProcess.push(SubtermPair(l->nthArgument(0), true, r->nthArgument(0), true));
        toProcess.push(SubtermPair(l->nthArgument(1), true, r->nthArgument(1), true));
        toProcess.push(SubtermPair(l->nthArgument(2), true, r->nthArgument(2), true));
        toProcess.push(SubtermPair(l->nthArgument(3), _splittable(lhs->nthArg(3)), 
                                   r->nthArgument(3), _splittable(rhs->nthArg(3))));         
      } else {
        for (unsigned i = 0; i < l->arity(); i++) {
          toProcess.push(SubtermPair(l->nthArgument(i), true, r->nthArgument(i), true));       
        }
      }
    } else {
      // different top
      unsigned x;
      if(!lhs->isSpecialVar()) {
        x = _nextVar++;
      #if REORDERING
        unresolvedSplits.insert(HOLUnresolvedSplitRecord(x,*lhs, pair.lhsSplittable()));
        lhs->makeSpecialVar(x);
      #else
        // TODO, this doesn't work with splitting currently
        Node::split(pnode,lhs,x);
      #endif
      } else {
        x=lhs->var();
      }
      svBindings.set(x, Subterm(*rhs, pair.rhsSplittable()));
    }
  }

  if (svBindings.isEmpty()) {
    ASS((*pnode)->isLeaf());
    ensureLeafEfficiency(reinterpret_cast<Leaf**>(pnode));
    Leaf* leaf = static_cast<Leaf*>(*pnode);
    leaf->insert(ld);
    DEBUG_INSERT("out: ", *this);
    return;
  }

  goto start;  
}

/*
 * Remove an entry from the substitution tree.
 *
 * @b pnode is pointer to root of tree corresponding to
 * top symbol of the term/literal being removed, and
 * @b bh contains its arguments.
 *
 * If the removal results in a chain of nodes containing
 * no terms/literals, all those nodes are removed as well.
 */
void HOLSubstitutionTree::higherOrderRemove(HOLBindingMap& svBindings, LeafData ld)
{
  CALL("SubstitutionTree::remove");
#define DEBUG_REMOVE(...)  //DBG(__VA_ARGS__)  
  ASS_EQ(_iterCnt,0);
  auto pnode = &_root;

  ASS(*pnode);

  DEBUG_REMOVE("remove: ", svBindings, " from ", *this)

  static Stack<Node**> history(1000);
  history.reset();

  while (! (*pnode)->isLeaf()) {
    history.push(pnode);

    IntermediateNode* inode=static_cast<IntermediateNode*>(*pnode);

    unsigned boundVar=inode->childVar;
    Subterm t = svBindings.get(boundVar);

    pnode=inode->childByTop(t.top(),false);
    ASS(pnode);


    TermList s = (*pnode)->term;
    ASS((*pnode)->top() == t.top());

    if(s==t.term()) {
      continue;
    }

    // computing the disagreement set of the two terms
    Stack<std::pair<TermList, Subterm>> subterms(120);

    subterms.push(std::make_pair(s, t));
    while (! subterms.isEmpty()) {
      auto pair = subterms.pop();

      auto treeTerm = pair.first;
      auto remvTerm = pair.second;

      if (treeTerm==remvTerm.term()) {
        continue;
      }
      if (treeTerm.isVar()) {
        ASS(treeTerm.isSpecialVar());
        svBindings.set(treeTerm.var(),remvTerm);
        continue;
      }
      ASS(!treeTerm.isVar());

      Term* l = treeTerm.term();
      Term* r = remvTerm.term().term(); 

      if(l->isApplication()){
        ASS(r->isApplication());
        subterms.push(std::make_pair((*l)[0], Subterm((*r)[0], true)));
        subterms.push(std::make_pair((*l)[1], Subterm((*r)[1], true)));
        subterms.push(std::make_pair((*l)[2], Subterm((*r)[2], true)));
        subterms.push(std::make_pair((*l)[3], Subterm((*r)[3], _splittable((*r)[3]))));
      } else {
        ASS(l->arity() == r->arity());
        for (unsigned i = 0; i < l->arity(); i++) {
          subterms.push(std::make_pair((*l)[i], Subterm((*r)[i], true)));
        }        
      }
    }
  }

  ASS ((*pnode)->isLeaf());


  Leaf* lnode = static_cast<Leaf*>(*pnode);
  lnode->remove(ld);
  ensureLeafEfficiency(reinterpret_cast<Leaf**>(pnode));

  while( (*pnode)->isEmpty() ) {
    if(history.isEmpty()) {
      delete *pnode;
      *pnode=0;
      DEBUG_REMOVE("out: ", *this);
      return;
    } else {
      Node* node=*pnode;
      IntermediateNode* parent=static_cast<IntermediateNode*>(*history.top());
      parent->remove((*pnode)->top());
      delete node;
      pnode=history.pop();
      ensureIntermediateNodeEfficiency(reinterpret_cast<IntermediateNode**>(pnode));
    }
  }
  DEBUG_REMOVE("out: ", *this);
} // SubstitutionTree::remove

} // namespace  Indexing

#endif

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
 * @file SubstitutionTree.cpp
 * Implements class SubstitutionTree.
 *
 * @since 16/08/2008 flight Sydney-San Francisco
 */

#include <utility>

#include "Shell/Options.hpp"

#include "Kernel/Matcher.hpp"
#include "Kernel/Renaming.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/ApplicativeHelper.hpp"

#include "Lib/BinaryHeap.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Recycled.hpp"
#include "Lib/DHMultiset.hpp"

#include "TermSharing.hpp"

#include <iostream>
#if VDEBUG
#include "Kernel/Signature.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"

#endif

#include "SubstitutionTree.hpp"

using namespace std;
using namespace Indexing;


/**
 * Initialise the substitution tree.
 * @since 16/08/2008 flight Sydney-San Francisco
 */
SubstitutionTree::SubstitutionTree(bool useC, bool rfSubs)
  : _nextVar(0)
  , _useC(useC)
  , _functionalSubtermMap(someIf(rfSubs, [](){ return FuncSubtermMap(); }))
  , _root(nullptr)
#if VDEBUG
  , _tag(false)
#endif
{
  CALL("SubstitutionTree::SubstitutionTree");

} // SubstitutionTree::SubstitutionTree

/**
 * Destroy the substitution tree.
 * @warning does not destroy nodes yet
 * @since 16/08/2008 flight Sydney-San Francisco
 */
SubstitutionTree::~SubstitutionTree()
{
  CALL("SubstitutionTree::~SubstitutionTree");
  ASS_EQ(_iterCnt,0);

  delete _root;
} // SubstitutionTree::~SubstitutionTree

/**
 * Store initial bindings of term @b t into @b bq.
 *
 * This method is used for insertions and deletions.
 */
void SubstitutionTree::getBindingsArgBindings(Term* t, BindingMap& svBindings)
{
  TermList* args=t->args();

  int nextVar = 0;
  while (! args->isEmpty()) {
    if (_nextVar <= nextVar) {
      ASS_EQ(_iterCnt,0);
      _nextVar = nextVar+1;
    }
    svBindings.insert(nextVar++, *args);
    args = args->next();
  }
}

struct UnresolvedSplitRecord
{
  UnresolvedSplitRecord() {}
  UnresolvedSplitRecord(unsigned var, TermList original)
  : var(var), original(original) {}

  unsigned var;
  TermList original;
};

struct BindingComparator
{
  static Comparison compare(const UnresolvedSplitRecord& r1, const UnresolvedSplitRecord& r2)
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
  static Comparison compare(const SubstitutionTree::Binding& b1, const SubstitutionTree::Binding& b2)
  {
#if REORDERING
    return Int::compare(b2.var,b1.var);
#else
    return Int::compare(b1.var,b2.var);
#endif
  }
};


/**
 * Insert an entry to the substitution tree.
 *
 * @b pnode is pointer to root of tree corresponding to
 * top symbol of the term/literal being inserted, and
 * @b bh contains its arguments.
 */
void SubstitutionTree::insert(BindingMap& svBindings, LeafData ld)
{
#define DEBUG_INSERT(...) // DBG(__VA_ARGS__)
  CALL("SubstitutionTree::insert");
  ASS_EQ(_iterCnt,0);
  auto pnode = &_root;
  DEBUG_INSERT("insert: ", svBindings, " into ", *this)

  if(*pnode == 0) {
    ASS(!svBindings.isEmpty())
    *pnode=createIntermediateNode(svBindings.getOneKey(),_useC);
  }
  if(svBindings.isEmpty()) {
    ASS((*pnode)->isLeaf());
    ensureLeafEfficiency(reinterpret_cast<Leaf**>(pnode));
    static_cast<Leaf*>(*pnode)->insert(ld);
    DEBUG_INSERT("out: ", *this);
    return;
  }

  typedef BinaryHeap<UnresolvedSplitRecord, BindingComparator> SplitRecordHeap;
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
	TermList term=svBindings.get(boundVar);
	bool wouldDescendIntoChild = inode->childByTop(term,false)!=0;
	ASS_EQ(wouldDescendIntoChild, TermList::sameTop(term, child->term));
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
	unresolvedSplits.insert(UnresolvedSplitRecord(inode->childVar, child->term));
	child->term=inode->term;
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
      UnresolvedSplitRecord urr=unresolvedSplits.pop();

      Node* node=*pnode;
      IntermediateNode* newNode = createIntermediateNode(node->term, urr.var,_useC);
      node->term=urr.original;

      *pnode=newNode;

      Node** nodePosition=newNode->childByTop(node->term, true);
      ASS(!*nodePosition);
      *nodePosition=node;
    }
  }
#endif
  ASS(!(*pnode)->isLeaf());

  IntermediateNode* inode = static_cast<IntermediateNode*>(*pnode);
  ASS(inode);

  unsigned boundVar=inode->childVar;
  TermList term=svBindings.get(boundVar);
  svBindings.remove(boundVar);

  //Into pparent we store the node, we might be inserting into.
  //So in the case we do insert, we might check whether this node
  //needs expansion.
  Node** pparent=pnode;
  pnode=inode->childByTop(term,true);

  if (*pnode == 0) {
    BindingMap::Iterator svit(svBindings);
    BinaryHeap<Binding, BindingComparator> remainingBindings;
    while (svit.hasNext()) {
      unsigned var;
      TermList term;
      svit.next(var, term);
      remainingBindings.insert(Binding(var, term));
    }
    while (!remainingBindings.isEmpty()) {
      Binding b=remainingBindings.pop();
      IntermediateNode* inode = createIntermediateNode(term, b.var,_useC);
      term=b.term;

      *pnode = inode;
      pnode = inode->childByTop(term,true);
    }
    Leaf* lnode=createLeaf(term);
    *pnode=lnode;
    lnode->insert(ld);

    ensureIntermediateNodeEfficiency(reinterpret_cast<IntermediateNode**>(pparent));
    DEBUG_INSERT("out: ", *this);
    return;
  }


  TermList* tt = &term;
  TermList* ss = &(*pnode)->term;

  ASS(TermList::sameTop(*ss, *tt));


  // ss is the term in node, tt is the term to be inserted
  // ss and tt have the same top symbols but are not equal
  // create the common subterm of ss,tt and an alternative node
  Stack<TermList*> subterms(64);
  for (;;) {
    if (*tt!=*ss && TermList::sameTop(*ss,*tt)) {
      // ss and tt have the same tops and are different, so must be non-variables
      ASS(! ss->isVar());
      ASS(! tt->isVar());

      Term* s = ss->term();
      Term* t = tt->term();

      ASS(s->arity() > 0);
      ASS(s->functor() == t->functor());

      if (s->shared()) {
        // create a shallow copy of s
        s = Term::cloneNonShared(s);
        ss->setTerm(s);
      }

      ss = s->args();
      tt = t->args();
      if (ss->next()->isEmpty()) {
        continue;
      }
      subterms.push(ss->next());
      subterms.push(tt->next());
    } else {
      if (! TermList::sameTop(*ss,*tt)) {
        unsigned x;
        if(!ss->isSpecialVar()) {
          x = _nextVar++;
        #if REORDERING
          unresolvedSplits.insert(UnresolvedSplitRecord(x,*ss));
          ss->makeSpecialVar(x);
        #else
          Node::split(pnode,ss,x);
        #endif
        } else {
          x=ss->var();
        }
        svBindings.set(x,*tt);
      }

      if (subterms.isEmpty()) {
        break;
      }
      tt = subterms.pop();
      ss = subterms.pop();
      if (! ss->next()->isEmpty()) {
        subterms.push(ss->next());
        subterms.push(tt->next());
      }
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
} // // SubstitutionTree::insert

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
void SubstitutionTree::remove(BindingMap& svBindings, LeafData ld)
{
  CALL("SubstitutionTree::remove");
  ASS_EQ(_iterCnt,0);
  auto pnode = &_root;

  ASS(*pnode);

  static Stack<Node**> history(1000);
  history.reset();

  while (! (*pnode)->isLeaf()) {
    history.push(pnode);

    IntermediateNode* inode=static_cast<IntermediateNode*>(*pnode);

    unsigned boundVar=inode->childVar;
    TermList t = svBindings.get(boundVar);

    pnode=inode->childByTop(t,false);
    ASS(pnode);


    TermList* s = &(*pnode)->term;
    ASS(TermList::sameTop(*s,t));

    if(*s==t) {
      continue;
    }

    ASS(! s->isVar());
    TermList* ss = s->term()->args();
    ASS(!ss->isEmpty());

    // computing the disagreement set of the two terms
    Stack<TermList*> subterms(120);

    subterms.push(ss);
    subterms.push(t.term()->args());
    while (! subterms.isEmpty()) {
      TermList* tt = subterms.pop();
      ss = subterms.pop();
      if (tt->next()->isEmpty()) {
	ASS(ss->next()->isEmpty());
      }
      else {
	subterms.push(ss->next());
	subterms.push(tt->next());
      }
      if (*ss==*tt) {
	continue;
      }
      if (ss->isVar()) {
	ASS(ss->isSpecialVar());
	svBindings.set(ss->var(),*tt);
	continue;
      }
      ASS(! tt->isVar());
      ASS(ss->term()->functor() == tt->term()->functor());
      ss = ss->term()->args();
      if (! ss->isEmpty()) {
	ASS(! tt->term()->args()->isEmpty());
	subterms.push(ss);
	subterms.push(tt->term()->args());
      }
    }
  }

  ASS ((*pnode)->isLeaf());


  Leaf* lnode = static_cast<Leaf*>(*pnode);
  lnode->remove(ld);
  ensureLeafEfficiency(reinterpret_cast<Leaf**>(pnode));

  while( (*pnode)->isEmpty() ) {
    TermList term=(*pnode)->term;
    if(history.isEmpty()) {
      delete *pnode;
      *pnode=0;
      return;
    } else {
      Node* node=*pnode;
      IntermediateNode* parent=static_cast<IntermediateNode*>(*history.top());
      parent->remove(term);
      delete node;
      pnode=history.pop();
      ensureIntermediateNodeEfficiency(reinterpret_cast<IntermediateNode**>(pnode));
    }
  }
} // SubstitutionTree::remove

/**
 * Return a pointer to the leaf that contains term specified by @b svBindings.
 * If no such leaf exists, return 0.
 */
SubstitutionTree::Leaf* SubstitutionTree::findLeaf(Node* root, BindingMap& svBindings)
{
  CALL("SubstitutionTree::findLeaf");
  ASS(root);

  Node* node=root;

  while (! node->isLeaf()) {
    IntermediateNode* inode=static_cast<IntermediateNode*>(node);

    unsigned boundVar=inode->childVar;
    TermList t = svBindings.get(boundVar);

    Node** child=inode->childByTop(t,false);
    if(!child) {
      return 0;
    }
    node=*child;


    TermList s = node->term;
    ASS(TermList::sameTop(s,t));

    if(s==t) {
      continue;
    }

    ASS(! s.isVar());
    TermList* ss = s.term()->args();
    ASS(!ss->isEmpty());

    // computing the disagreement set of the two terms
    Stack<TermList*> subterms(120);

    subterms.push(ss);
    subterms.push(t.term()->args());
    while (! subterms.isEmpty()) {
      TermList* tt = subterms.pop();
      ss = subterms.pop();
      if (tt->next()->isEmpty()) {
	ASS(ss->next()->isEmpty());
      }
      else {
	subterms.push(ss->next());
	subterms.push(tt->next());
      }
      if (*ss==*tt) {
	continue;
      }
      if (ss->isSpecialVar()) {
	svBindings.set(ss->var(),*tt);
	continue;
      }
      if(ss->isVar() || tt->isVar() || ss->term()->functor()!=tt->term()->functor()) {
	return 0;
      }
      ss = ss->term()->args();
      if (! ss->isEmpty()) {
	ASS(! tt->term()->args()->isEmpty());
	subterms.push(ss);
	subterms.push(tt->term()->args());
      }
    }
  }
  ASS(node->isLeaf());
  return static_cast<Leaf*>(node);
}


#if VDEBUG

vstring getIndentStr(int n)
{
  vstring res;
  for(int indCnt=0;indCnt<n;indCnt++) {
	res+="  ";
  }
  return res;
}

#endif

SubstitutionTree::Node::~Node()
{
  CALL("SubstitutionTree::Node::~Node");

  if(term.isTerm()) {
    term.term()->destroyNonShared();
  }
}


void SubstitutionTree::Node::split(Node** pnode, TermList* where, int var)
{
  CALL("SubstitutionTree::Node::split");

  Node* node=*pnode;

  IntermediateNode* newNode = createIntermediateNode(node->term, var,node->withSorts());
  node->term=*where;
  *pnode=newNode;

  where->makeSpecialVar(var);

  Node** nodePosition=newNode->childByTop(node->term, true);
  ASS(!*nodePosition);
  *nodePosition=node;
}

void SubstitutionTree::IntermediateNode::loadChildren(NodeIterator children)
{
  CALL("SubstitutionTree::IntermediateNode::loadChildren");

  while(children.hasNext()) {
    Node* ext=*children.next();
    Node** own=childByTop(ext->term, true);
    ASS(! *own);
    *own=ext;
  }
}

void SubstitutionTree::Leaf::loadChildren(LDIterator children)
{
  CALL("SubstitutionTree::Leaf::loadClauses");

  while(children.hasNext()) {
    LeafData ld=children.next();
    insert(ld);
  }
}

SubstitutionTree::LeafIterator::LeafIterator(SubstitutionTree* st)
  : _curr()
  , _nodeIterators()
{
  if (st->_root->isLeaf()) {
    _curr = st->_root;
  } else {
    _curr = nullptr;
    _nodeIterators.push(static_cast<IntermediateNode*>(st->_root)->allChildren());
  }
}

SubstitutionTree::Leaf* SubstitutionTree::LeafIterator::next()
{
  ASS(_curr->isLeaf());
  auto out = _curr;
  skipToNextLeaf();
  return static_cast<Leaf*>(out);
}


void SubstitutionTree::LeafIterator::skipToNextLeaf()
{
  for (;;) {
    while(!_nodeIterators.isEmpty() && !_nodeIterators.top().hasNext()) {
      _nodeIterators.pop();
      _curr = nullptr;
    }
    if (_nodeIterators.isEmpty()) {
      ASS_EQ(_curr,0)
      return;
    } else {
      _curr = *_nodeIterators.top().next();
      if (_curr->isLeaf()) {
        return;
      } else {
        _nodeIterators.push(static_cast<IntermediateNode*>(_curr)->allChildren());
        _curr = nullptr;
      }
    }
  }
}

bool SubstitutionTree::LeafIterator::hasNext()
{
  CALL("SubstitutionTree::Leaf::hasNext");
  return _curr != nullptr;
}

SubstitutionTree::UnificationsIterator::~UnificationsIterator()
{
  if(_clientBDRecording) {
    _subst->bdDone();
    _clientBDRecording=false;
    _clientBacktrackData.backtrack();
  }
  if (_bdStack) 
    while(_bdStack->isNonEmpty()) {
      _bdStack->pop().backtrack();
    }
}

bool SubstitutionTree::UnificationsIterator::hasNext()
{
  CALL("SubstitutionTree::UnificationsIterator::hasNext");

  if(_clientBDRecording) {
    _subst->bdDone();
    _clientBDRecording=false;
    _clientBacktrackData.backtrack();
  }

  while(!_ldIterator.hasNext() && findNextLeaf()) {}
  return _ldIterator.hasNext();
}

SubstitutionTree::QueryResult SubstitutionTree::UnificationsIterator::next()
{
  CALL("SubstitutionTree::UnificationsIterator::next");

  while(!_ldIterator.hasNext() && findNextLeaf()) {}
  ASS(_ldIterator.hasNext());

  ASS(!_clientBDRecording);

  LeafData& ld=_ldIterator.next();

  if(_retrieveSubstitution) {
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
    _subst->bdRecord(_clientBacktrackData);
    _clientBDRecording=true;

    _subst->denormalize(normalizer,NORM_RESULT_BANK,RESULT_BANK);

    return QueryResult(ld, ResultSubstitution::fromSubstitution( &*_subst, QUERY_BANK, RESULT_BANK),
        // TODO do we really wanna copy the whole constraints stack here?
            UnificationConstraintStackSP(new UnificationConstraintStack(*_constraints))); 
  } else {
    return QueryResult(ld);
  }
}


bool SubstitutionTree::UnificationsIterator::findNextLeaf()
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

bool SubstitutionTree::UnificationsIterator::enter(Node* n, BacktrackData& bd)
{
  CALL("SubstitutionTree::UnificationsIterator::enter");

#if VDEBUG
  if(_tag){
    cout << "=========================================" << endl;
    cout << "entering..." << *n << endl;
    cout << "subst is " << _subst << endl;
    cout << "svstack is " << _svStack << endl;
    cout << "=========================================" << endl;
  } 
#endif

  bool success=true;
  bool recording=false;
  if(!n->term.isEmpty()) {
    //n is proper node, not a root

    TermList qt(_svStack->top(), true);

    recording=true;
    _subst->bdRecord(bd);
    success=associate(qt,n->term,bd);
  }
  if(success) {
    if(n->isLeaf()) {
      _ldIterator=static_cast<Leaf*>(n)->allChildren();
      _inLeaf=true;
    } else {
      IntermediateNode* inode=static_cast<IntermediateNode*>(n);
      _svStack->push(inode->childVar);
      NodeIterator nit=getNodeIterator(inode);
      if(_useUWAConstraints){
        TermList qt = _subst->getSpecialVarTop(inode->childVar);
        NodeIterator enit = pvi(getConcatenatedIterator(inode->childBySort(qt),nit));
        _nodeIterators->backtrackablePush(enit,bd);
      }
      else{
        _nodeIterators->backtrackablePush(nit, bd);
      }
    }
  }
  if(recording) {
    _subst->bdDone();
  }
  return success;
}

bool SubstitutionTree::SubstitutionTreeMismatchHandler::introduceConstraint(TermList query,unsigned index1, TermList node,unsigned index2)
{
  CALL("SubstitutionTree::MismatchHandler::introduceConstraint");
  
  auto constraint = make_pair(make_pair(query,index1),make_pair(node,index2));
  _constraints.backtrackablePush(constraint,_bd);
  return true;
}

bool SubstitutionTree::STHOMismatchHandler::handle
     (RobSubstitution* subst,TermList query,unsigned index1, TermList node,unsigned index2)
{
  CALL("SubstitutionTree::STHOMismatchHandler::handle");

  auto constraint = make_pair(make_pair(query,index1),make_pair(node,index2));
  _constraints.backtrackablePush(constraint,_bd);
  return true;
}

/**
 * TODO: explain properly what associate does
 * called from enter(...)
 */
bool SubstitutionTree::UnificationsIterator::associate(TermList query, TermList node, BacktrackData& bd)
{
  CALL("SubstitutionTree::UnificationsIterator::associate");

  //The ordering of the if statements is important here. Higher-order problems
  //should never require theory resoning (at the moment, theories cannot be parsed in HOL)
  //However, a user can still set UWA option on. We don't wan't that to result in 
  //the wrong handler being used.
  if(_useHOConstraints){
    STHOMismatchHandler hndlr(*_constraints,bd);
    return _subst->unify(query,QUERY_BANK,node,NORM_RESULT_BANK,&hndlr);    
  }
  if(_useUWAConstraints){ 
    SubstitutionTreeMismatchHandler hndlr(*_constraints,bd);
    return _subst->unify(query,QUERY_BANK,node,NORM_RESULT_BANK,&hndlr);
  } 
  return _subst->unify(query,QUERY_BANK,node,NORM_RESULT_BANK);
}

//TODO I think this works for VSpcialVars as well. Since .isVar() will return true 
//for them
SubstitutionTree::NodeIterator SubstitutionTree::UnificationsIterator::getNodeIterator(IntermediateNode* n)
{
  CALL("SubstitutionTree::UnificationsIterator::getNodeIterator");

  unsigned specVar=n->childVar;
  TermList qt=_subst->getSpecialVarTop(specVar);
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

void SubstitutionTree::Leaf::output(std::ostream& out, bool multiline, int indent) const 
{ out << this->term; }

void SubstitutionTree::IntermediateNode::output(std::ostream& out, bool multiline, int indent) const 
{
  // TODO const version of allChildren
  auto childIter = iterTraits(((IntermediateNode*)this)->allChildren());
  if (!this->term.isEmpty()) {
    out << this->term
        << " ; ";
  }
  out << "S" << this->childVar << " -> ";

  auto first = childIter.next();
  auto brackets = childIter.hasNext();
  if (brackets) {


    if (multiline) {
      auto outp = [&](Node** x) { 
        out << endl; 
        repeat(out, INDENT, indent + 1);
        out << "| ";
        (*x)->output(out, multiline, indent + 1);
      };
      out << "[";
      outp(first);
      while (childIter.hasNext()) {
        outp(childIter.next());
      }
      out << endl; 
      repeat(out, INDENT, indent);
      out << "]";

    } else {
      out << "[ ";
      out << **first;
      while (childIter.hasNext()) {
        out <<  " | " << **childIter.next();
      } 
      out << " ]";
    }


  } else {
    (*first)->output(out, multiline, indent);
  }

}


#define VERBOSE_OUTPUT_OPERATORS 0

std::ostream& Indexing::operator<<(std::ostream& out, SubstitutionTree const& self)
{
#if VERBOSE_OUTPUT_OPERATORS
  out << "{ nextVar: S" << self._nextVar << ", root: (";
#endif // VERBOSE_OUTPUT_OPERATORS
  if (self._root) {
    out << *self._root;
  } else {
    out << "<empty tree>";
  }
#if VERBOSE_OUTPUT_OPERATORS
  out << ") }";
#endif // VERBOSE_OUTPUT_OPERATORS
  return out;
}



std::ostream& Indexing::operator<<(std::ostream& out, OutputMultiline<SubstitutionTree> const& self)
{
  if (self.self._root) {
    self.self._root->output(out, true, /* indent */ 0);
  } else {
    out << "<empty tree>";
  }
  return out;
}



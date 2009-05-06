/**
 * @file SubstitutionTree.cpp
 * Implements class SubstitutionTree.
 *
 * @since 16/08/2008 flight Sydney-San Francisco
 */

#include <utility>

#include "../Kernel/Matcher.hpp"
#include "../Kernel/Renaming.hpp"
#include "../Kernel/SubstHelper.hpp"
#include "../Kernel/Term.hpp"

#include "../Lib/BinaryHeap.hpp"
#include "../Lib/Metaiterators.hpp"
#include "../Lib/Environment.hpp"
#include "../Lib/Recycler.hpp"
#include "../Lib/DHMultiset.hpp"

#include "TermSharing.hpp"

#include <iostream>
#if VDEBUG
#include "../Kernel/Signature.hpp"
#include "../Lib/Environment.hpp"
#include "../Lib/Int.hpp"
#include "../Test/Output.hpp"

string SingleTermListToString(const TermList* ts);

#endif

#include "SubstitutionTree.hpp"

using namespace std;
using namespace Indexing;




/**
 * Initialise the substitution tree.
 * @since 16/08/2008 flight Sydney-San Francisco
 */
SubstitutionTree::SubstitutionTree(int nodes)
  : _nextVar(0), _nodes(nodes)
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
  for (unsigned i = 0; i<_nodes.size(); i++) {
    if(_nodes[i]!=0) {
      delete _nodes[i];
    }
  }
} // SubstitutionTree::~SubstitutionTree

/**
 * Store initial bindings of term @b t into @b bq.
 *
 * This method is used for insertions and deletions.
 */
void SubstitutionTree::getBindings(Term* t, BindingMap& svBindings)
{
  TermList* args=t->args();

  int nextVar = 0;
  while (! args->isEmpty()) {
    if (_nextVar <= nextVar) {
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
void SubstitutionTree::insert(Node** pnode,BindingMap& svBindings,LeafData ld)
{
  CALL("SubstitutionTree::insert/3");

  if(*pnode == 0) {
    if(svBindings.isEmpty()) {
      *pnode=createLeaf();
    } else {
      *pnode=createIntermediateNode(svBindings.getOneKey());
    }
  }
  if(svBindings.isEmpty()) {
    ASS((*pnode)->isLeaf());
    ensureLeafEfficiency(reinterpret_cast<Leaf**>(pnode));
    static_cast<Leaf*>(*pnode)->insert(ld);
    return;
  }

  typedef BinaryHeap<UnresolvedSplitRecord, BindingComparator> SplitRecordHeap;
  static SplitRecordHeap unresolvedSplits;
  unresolvedSplits.reset();

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
      IntermediateNode* newNode = createIntermediateNode(node->term, urr.var);
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
      Binding b;
      svit.next(b.var, b.term);
      remainingBindings.insert(b);
    }
    while (!remainingBindings.isEmpty()) {
      Binding b=remainingBindings.pop();
      IntermediateNode* inode = createIntermediateNode(term, b.var);
      term=b.term;

      *pnode = inode;
      pnode = inode->childByTop(term,true);
    }
    Leaf* lnode=createLeaf(term);
    *pnode=lnode;
    lnode->insert(ld);

    ensureIntermediateNodeEfficiency(reinterpret_cast<IntermediateNode**>(pparent));
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
void SubstitutionTree::remove(Node** pnode,BindingMap& svBindings,LeafData ld)
{
  CALL("SubstitutionTree::remove-2");

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
  CALL("SubstitutionTree::remove-2");
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
  ASS(node->isLeaf());
  return static_cast<Leaf*>(node);
}


#if VDEBUG

string getIndentStr(int n)
{
  string res;
  for(int indCnt=0;indCnt<n;indCnt++) {
	res+="  ";
  }
  return res;
}

string SubstitutionTree::nodeToString(Node* topNode)
{
  string res;
  Stack<int> indentStack(10);
  Stack<Node*> stack(10);

  stack.push(topNode);
  indentStack.push(1);

  while(stack.isNonEmpty()) {
    Node* node=stack.pop();
    int indent=indentStack.pop();

    if(!node) {
	continue;
    }
    if(!node->term.isEmpty()) {
      res+=getIndentStr(indent)+Test::Output::singleTermListToString(node->term)+"\n";
    }

    if(node->isLeaf()) {
	Leaf* lnode = static_cast<Leaf*>(node);
	LDIterator ldi(lnode->allChildren());

	while(ldi.hasNext()) {
	  res+=getIndentStr(indent) + "Lit: " + ldi.next().literal->toString() + "\n";
	}
    } else {
	IntermediateNode* inode = static_cast<IntermediateNode*>(node);
	NodeIterator noi(inode->allChildren());
	while(noi.hasNext()) {
	  stack.push(*noi.next());
	  indentStack.push(indent+1);
	}
    }
  }
  return res;
}

string SubstitutionTree::toString() const
{
  CALL("SubstitutionTree::toString");

  string res;

  for(unsigned tli=0;tli<_nodes.size();tli++) {
    res+=Int::toString(tli);
    res+=":\n";

    Stack<int> indentStack(10);
    Stack<Node*> stack(10);

    res+=nodeToString(_nodes[tli]);
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

  IntermediateNode* newNode = createIntermediateNode(node->term, var);
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

bool SubstitutionTree::LeafIterator::hasNext()
{
  for(;;) {
    while(!_nodeIterators.isEmpty() && !_nodeIterators.top().hasNext()) {
      _nodeIterators.pop();
    }
    if(_nodeIterators.isEmpty()) {
      do {
	if(_nextRootPtr==_afterLastRootPtr) {
	  return false;
	}
	_curr=*(_nextRootPtr++);
      } while(_curr==0);
    } else {
      _curr=*_nodeIterators.top().next();
    }
    if(_curr->isLeaf()) {
      return true;
    } else {
      _nodeIterators.push(static_cast<IntermediateNode*>(_curr)->allChildren());
    }
  }
}

SubstitutionTree::UnificationsIterator::UnificationsIterator(SubstitutionTree* parent,
	Node* root, Term* query, bool retrieveSubstitution, bool reversed)
: svStack(32), literalRetrieval(query->isLiteral()),
  retrieveSubstitution(retrieveSubstitution), inLeaf(false),
ldIterator(LDIterator::getEmpty()), nodeIterators(8), bdStack(8),
clientBDRecording(false)
{
  CALL("SubstitutionTree::UnificationsIterator::UnificationsIterator");

  if(!root) {
    return;
  }

  queryNormalizer.normalizeVariables(query);
  Term* queryNorm=queryNormalizer.apply(query);

  if(reversed) {
    createReversedInitialBindings(queryNorm);
  } else {
    createInitialBindings(queryNorm);
  }

  BacktrackData bd;
  enter(root, bd);
  bd.drop();
}

SubstitutionTree::UnificationsIterator::~UnificationsIterator()
{
  if(clientBDRecording) {
    subst.bdDone();
    clientBDRecording=false;
    clientBacktrackData.backtrack();
  }
  while(bdStack.isNonEmpty()) {
    bdStack.pop().backtrack();
  }
}

void SubstitutionTree::UnificationsIterator::createInitialBindings(Term* t)
{
  CALL("SubstitutionTree::UnificationsIterator::createInitialBindings");

  TermList* args=t->args();
  int nextVar = 0;
  while (! args->isEmpty()) {
    unsigned var = nextVar++;
    subst.bindSpecialVar(var,*args,NORM_QUERY_BANK);
    args = args->next();
  }
}

void SubstitutionTree::UnificationsIterator::createReversedInitialBindings(Term* t)
{
  CALL("SubstitutionTree::UnificationsIterator::createReversedInitialBindings");
  ASS(t->isLiteral());
  ASS(t->commutative());
  ASS_EQ(t->arity(),2);

  subst.bindSpecialVar(1,*t->nthArgument(0),NORM_QUERY_BANK);
  subst.bindSpecialVar(0,*t->nthArgument(1),NORM_QUERY_BANK);
}

bool SubstitutionTree::UnificationsIterator::hasNext()
{
  CALL("SubstitutionTree::UnificationsIterator::hasNext");

  if(clientBDRecording) {
    subst.bdDone();
    clientBDRecording=false;
    clientBacktrackData.backtrack();
  }

  while(!ldIterator.hasNext() && findNextLeaf()) {}
  return ldIterator.hasNext();
}

SubstitutionTree::QueryResult SubstitutionTree::UnificationsIterator::next()
{
  CALL("SubstitutionTree::UnificationsIterator::next");

  while(!ldIterator.hasNext() && findNextLeaf()) {}
  ASS(ldIterator.hasNext());

  ASS(!clientBDRecording);

  LeafData& ld=ldIterator.next();

  if(retrieveSubstitution) {
    Renaming normalizer;
    if(literalRetrieval) {
      normalizer.normalizeVariables(ld.literal);
    } else {
      normalizer.normalizeVariables(ld.term);
    }

    ASS(clientBacktrackData.isEmpty());
    subst.bdRecord(clientBacktrackData);
    clientBDRecording=true;

    subst.denormalize(normalizer,NORM_RESULT_BANK,RESULT_BANK);
    subst.denormalize(queryNormalizer,NORM_QUERY_BANK,QUERY_BANK);

    return QueryResult(&ld, ResultSubstitution::fromSubstitution(
	    &subst, QUERY_BANK, RESULT_BANK));
  } else {
    return QueryResult(&ld, ResultSubstitutionSP());
  }
}


bool SubstitutionTree::UnificationsIterator::findNextLeaf()
{
  CALL("SubstitutionTree::UnificationsIterator::findNextLeaf");

  if(nodeIterators.isEmpty()) {
    //There are no node iterators in the stack, so there's nowhere
    //to look for the next leaf.
    //This shouldn't hapen during the regular retrieval process, but it
    //can happen when there are no literals inserted for a predicate,
    //or when predicates with zero arity are encountered.
    ASS(bdStack.isEmpty());
    return false;
  }

  if(inLeaf) {
    ASS(!clientBDRecording);
    //Leave the current leaf
    bdStack.pop().backtrack();
    inLeaf=false;
  }

  ASS(!clientBDRecording);
  ASS(bdStack.length()+1==nodeIterators.length());

  do {
    while(!nodeIterators.top().hasNext() && !bdStack.isEmpty()) {
      //backtrack undos everything that enter(...) method has done,
      //so it also pops one item out of the nodeIterators stack
      bdStack.pop().backtrack();
      svStack.pop();
    }
    if(!nodeIterators.top().hasNext()) {
      return false;
    }
    Node* n=*nodeIterators.top().next();
    BacktrackData bd;
    bool success=enter(n,bd);
    if(!success) {
      bd.backtrack();
      continue;
    } else {
      bdStack.push(bd);
    }
  } while(!inLeaf);
  return true;
}

bool SubstitutionTree::UnificationsIterator::enter(Node* n, BacktrackData& bd)
{
  CALL("SubstitutionTree::UnificationsIterator::enter");

  bool success=true;
  bool recording=false;
  if(!n->term.isEmpty()) {
    //n is proper node, not a root

    TermList qt(svStack.top(), true);

    recording=true;
    subst.bdRecord(bd);
    success=associate(qt,n->term);
  }
  if(success) {
    if(n->isLeaf()) {
      ldIterator=static_cast<Leaf*>(n)->allChildren();
      inLeaf=true;
    } else {
      IntermediateNode* inode=static_cast<IntermediateNode*>(n);
      svStack.push(inode->childVar);
      NodeIterator nit=getNodeIterator(inode);
      nodeIterators.backtrackablePush(nit, bd);
    }
  }
  if(recording) {
    subst.bdDone();
  }
  return success;
}

bool SubstitutionTree::UnificationsIterator::associate(TermList query, TermList node)
{
  CALL("SubstitutionTree::UnificationsIterator::associate");
  return subst.unify(query,NORM_QUERY_BANK,node,NORM_RESULT_BANK);
}

SubstitutionTree::NodeIterator
  SubstitutionTree::UnificationsIterator::getNodeIterator(IntermediateNode* n)
{
  CALL("SubstitutionTree::UnificationsIterator::getNodeIterator");

  unsigned specVar=n->childVar;
  TermList qt=subst.getSpecialVarTop(specVar);
  if(qt.isVar()) {
	return n->allChildren();
  } else {
	Node** match=n->childByTop(qt, false);
	if(match) {
	  return pvi( getConcatenatedIterator(
			  getSingletonIterator(match),
			  n->variableChildren()) );
	} else {
	  return n->variableChildren();
	}
  }
}

bool SubstitutionTree::GeneralizationsIterator::associate(TermList query, TermList node)
{
  CALL("SubstitutionTree::GeneralizationsIterator::associate");
  return subst.match(node, NORM_RESULT_BANK, query, NORM_QUERY_BANK);
}

SubstitutionTree::NodeIterator
  SubstitutionTree::GeneralizationsIterator::getNodeIterator(IntermediateNode* n)
{
  CALL("SubstitutionTree::GeneralizationsIterator::getNodeIterator");

  unsigned specVar=n->childVar;
  TermList qt=subst.getSpecialVarTop(specVar);
  if(qt.isVar()) {
	return n->variableChildren();
  } else {
	Node** match=n->childByTop(qt, false);
	if(match) {
	  return pvi( getConcatenatedIterator(getSingletonIterator(match),
		  n->variableChildren()) );
	} else {
	  return n->variableChildren();
	}
  }
}


bool SubstitutionTree::InstancesIterator::associate(TermList query, TermList node)
{
  CALL("SubstitutionTree::InstancesIterator::associate");
  return subst.match(query, NORM_QUERY_BANK, node, NORM_RESULT_BANK);
}

SubstitutionTree::NodeIterator
  SubstitutionTree::InstancesIterator::getNodeIterator(IntermediateNode* n)
{
  CALL("SubstitutionTree::GeneralizationsIterator::getNodeIterator");

  unsigned specVar=n->childVar;
  TermList qt=subst.getSpecialVarTop(specVar);
  if(qt.isVar()) {
	return n->allChildren();
  } else {
	Node** match=n->childByTop(qt, false);
	if(match) {
	  return pvi( getSingletonIterator(match) );
	} else {
	  return NodeIterator::getEmpty();
	}
  }
}


/**
 * Binding structure to be passed to the @b MatchingUtils::matchArgs
 * method.
 */
struct SubstitutionTree::GenMatcher::Binder
{
  /**
   * Create Binder structure for @b _parent. Use @b newSpecVars
   * to store numbers of special variables, that were bound by
   * this object.
   */
  inline
  Binder(GenMatcher* parent)
  : _parent(parent), _maxVar(parent->_maxVar) {}
  /**
   * Ensure variable @b var is bound to @b term. Return false iff
   * it is not possible. If a new binding was creater, push @b var
   * onto parent's @b _boundVars stack.
   */
  bool bind(unsigned var, TermList term)
  {
    if(var > _maxVar) {
      return false;
    }
    TermList* aux;
    if(_parent->_bindings->getValuePtr(var,aux,term)) {
      _parent->_boundVars.push(var);
      return true;
    } else {
      return *aux==term;
    }
  }
  /**
   * Bind special variable @b var to @b term, and push @b var
   * onto @b _newSpecVars stack.
   */
  inline
  void specVar(unsigned var, TermList term)
  {
    (*_parent->_specVars)[var]=term;
  }
private:
  GenMatcher* _parent;
  /**
   * Maximal number of boundable ordinary variable. If binding
   * bigger variable is attempted, it fails.
   */
  unsigned _maxVar;
};

struct SubstitutionTree::GenMatcher::Applicator
{
  inline
  Applicator(GenMatcher* parent, Renaming* resultNormalizer)
  : _parent(parent), _resultNormalizer(resultNormalizer) {}
  TermList apply(unsigned var)
  {
    TermList* cacheEntry;
    if(_cache.getValuePtr(var,cacheEntry)) {
      ASS(_resultNormalizer->contains(var));
      unsigned nvar=_resultNormalizer->get(var);
      ASS(_parent->_bindings->find(nvar));
      *cacheEntry=_parent->_bindings->get(nvar);
    }
    return *cacheEntry;
  }
private:
  GenMatcher* _parent;
  Renaming* _resultNormalizer;
  BindingMap _cache;
};

class SubstitutionTree::GenMatcher::Substitution
: public ResultSubstitution
{
public:
  Substitution(GenMatcher* parent, Renaming* resultNormalizer)
  : _parent(parent), _resultNormalizer(resultNormalizer),
  _applicator(0)
  {}
  ~Substitution()
  {
    if(_applicator) {
      delete _applicator;
    }
  }

  TermList applyToBoundResult(TermList t)
  { return SubstHelper::apply(t, *getApplicator()); }

  bool isIdentityOnQueryWhenResultBound() {return true;}
private:
  Applicator* getApplicator()
  {
    if(!_applicator) {
      _applicator=new Applicator(_parent, _resultNormalizer);
    }
    return _applicator;
  }

  GenMatcher* _parent;
  Renaming* _resultNormalizer;
  Applicator* _applicator;
};

/**
 * @b nextSpecVar Number higher than any special variable present in the tree.
 * 	It's used to determine size of the array that stores bindings of
 * 	special variables.
 */
SubstitutionTree::GenMatcher::GenMatcher(Term* query, unsigned nextSpecVar)
: _boundVars(256)
{
  Recycler::get(_specVars);
  if(_specVars->size()<nextSpecVar) {
    //_specVars can get really big, but it was introduced instead of hash table
    //during optimizations, as it raised performance by abour 5%.
    _specVars->ensure(_specVars->size()*2);
  }
  Recycler::get(_bindings);

  _maxVar=query->weight()-1;
  _bindings->ensure(query->weight());
}
SubstitutionTree::GenMatcher::~GenMatcher()
{
  Recycler::release(_bindings);
  Recycler::release(_specVars);
}

/**
 * Match special variable, that is about to be matched next during
 * iterator's traversal through the tree, to @b nodeTerm.
 *
 * @param separate If true, join this match with the previous one
 * 	on backtracking stack, so they will be undone both by one
 * 	call to the @b backtrack() method.
 */
bool SubstitutionTree::GenMatcher::matchNext(unsigned specVar, TermList nodeTerm, bool separate)
{
  CALL("SubstitutionTree::GenMatcher::matchNext");

  if(separate) {
    _boundVars.push(BACKTRACK_SEPARATOR);
  }

  TermList queryTerm=(*_specVars)[specVar];
  ASSERT_VALID(queryTerm);

  bool success;
  if(nodeTerm.isTerm()) {
    Term* nt=nodeTerm.term();
    if(nt->shared() && nt->ground()) {
      //ground terms match only iff they're equal
      success = nodeTerm==queryTerm;
    } else {
      Binder binder(this);
      ASS(nt->arity()>0);

      success = queryTerm.isTerm() && queryTerm.term()->functor()==nt->functor() &&
	MatchingUtils::matchArgs(nt, queryTerm.term(), binder);
    }
  } else {
    ASS_METHOD(nodeTerm,isOrdinaryVar());
    unsigned var=nodeTerm.var();
    Binder binder(this);
    success=binder.bind(var,queryTerm);
  }

  if(!success) {
    //if this matching was joined to the previous one, we don't
    //have to care about unbinding as caller will do this by calling
    //backtrack for the matching we're joined to.
    if(separate) {
      //we have to unbind ordinary variables, that were bound.
      for(;;) {
	unsigned boundVar=_boundVars.pop();
	if(boundVar==BACKTRACK_SEPARATOR) {
	  break;
	}
	_bindings->remove(boundVar);
      }
    }
  }
  return success;
}

/**
 * Undo one call to the @b matchNext method with separate param
 * set to @b true and all other @b matchNext calls that were joined to it.
 */
void SubstitutionTree::GenMatcher::backtrack()
{
  CALL("SubstitutionTree::GenMatcher::backtrack");

  for(;;) {
    unsigned boundVar=_boundVars.pop();
    if(boundVar==BACKTRACK_SEPARATOR) {
      break;
    }
    _bindings->remove(boundVar);
  }
}

/**
 * Try to undo one call to the @b matchNext method with separate param
 * set to @b true and all other @b matchNext calls that were joined to it.
 * Return true iff successful. (The failure can be due to the fact there
 * is no separated @b matchNext call to be undone. In this case every binding
 * on the @b _boundVars stack would be undone.)
 */
bool SubstitutionTree::GenMatcher::tryBacktrack()
{
  CALL("SubstitutionTree::GenMatcher::tryBacktrack");

  while(_boundVars.isNonEmpty()) {
    unsigned boundVar=_boundVars.pop();
    if(boundVar==BACKTRACK_SEPARATOR) {
      return true;
    }
    _bindings->remove(boundVar);
  }
  return false;
}


ResultSubstitutionSP SubstitutionTree::GenMatcher::getSubstitution(
	Renaming* resultNormalizer)
{
  return ResultSubstitutionSP(
	  new Substitution(this, resultNormalizer));
}

/**
 * @param nextSpecVar first unassigned special variable. Is being used
 * 	to determine size of array, that stores special variable bindings.
 * 	(To maximize performance, a DArray object is being used instead
 * 	of hash map.)
 * @param reversed If true, parameters of supplied binary literal are
 * 	reversed. (useful for retrieval commutative terms)
 */
SubstitutionTree::FastGeneralizationsIterator::FastGeneralizationsIterator(
	SubstitutionTree* parent, Node* root,
	Term* query, bool retrieveSubstitution, bool reversed)
: _subst(query,parent->_nextVar), _literalRetrieval(query->isLiteral()), _retrieveSubstitution(retrieveSubstitution),
  _inLeaf(false), _ldIterator(LDIterator::getEmpty()),
  _root(root), _alternatives(64), _specVarNumbers(64), _nodeTypes(64)
{
  CALL("SubstitutionTree::FastGeneralizationsIterator::FastGeneralizationsIterator");
  ASS(root);
  ASS(!root->isLeaf());

  if(reversed) {
    createReversedInitialBindings(query);
  } else {
    createInitialBindings(query);
  }

}

void SubstitutionTree::FastGeneralizationsIterator::createInitialBindings(Term* t)
{
  CALL("SubstitutionTree::FastGeneralizationsIterator::createInitialBindings");

  TermList* args=t->args();
  int nextVar = 0;
  while (! args->isEmpty()) {
    unsigned var = nextVar++;
    _subst.bindSpecialVar(var,*args);
    args = args->next();
  }
}

/**
 * For a binary comutative query literal, create initial bindings,
 * where the order of special variables is reversed.
 */
void SubstitutionTree::FastGeneralizationsIterator::createReversedInitialBindings(Term* t)
{
  CALL("SubstitutionTree::FastGeneralizationsIterator::createReversedInitialBindings");
  ASS(t->isLiteral());
  ASS(t->commutative());
  ASS_EQ(t->arity(),2);

  _subst.bindSpecialVar(1,*t->nthArgument(0));
  _subst.bindSpecialVar(0,*t->nthArgument(1));
}

bool SubstitutionTree::FastGeneralizationsIterator::hasNext()
{
  CALL("SubstitutionTree::FastGeneralizationsIterator::hasNext");

  while(!_ldIterator.hasNext() && findNextLeaf()) {}
  return _ldIterator.hasNext();
}

SubstitutionTree::QueryResult SubstitutionTree::FastGeneralizationsIterator::next()
{
  CALL("SubstitutionTree::FastGeneralizationsIterator::next");

  while(!_ldIterator.hasNext() && findNextLeaf()) {}
  ASS(_ldIterator.hasNext());
  LeafData& ld=_ldIterator.next();

  if(_retrieveSubstitution) {
    _resultNormalizer.reset();
    if(_literalRetrieval) {
      _resultNormalizer.normalizeVariables(ld.literal);
    } else {
      _resultNormalizer.normalizeVariables(ld.term);
    }

    return QueryResult(&ld,
	    _subst.getSubstitution(&_resultNormalizer));
  } else {
    return QueryResult(&ld, ResultSubstitutionSP());
  }
}


/**
 * Find next leaf, that contains generalizations of the query
 * term. If there is no such, return false.
 */
bool SubstitutionTree::FastGeneralizationsIterator::findNextLeaf()
{
  CALL("SubstitutionTree::FastGeneralizationsIterator::findNextLeaf");

  Node* curr;
  bool sibilingsRemain;
  if(_inLeaf) {
    if(_alternatives.isEmpty()) {
      return false;
    }
    _subst.backtrack();
    _inLeaf=false;
    curr=0;
  } else {
    //this should happen only the first time the method is called
    //and so we're not in any leaf yet
    ASS(_root);
    curr=_root;
    _root=0;
    sibilingsRemain=enterNode(curr);
  }
  for(;;) {
main_loop_start:
    unsigned currSpecVar;

    if(curr) {
      if(sibilingsRemain) {
	ASS(_nodeTypes.top()!=UNSORTED_LIST || *static_cast<Node**>(_alternatives.top()));
	currSpecVar=_specVarNumbers.top();
      } else {
	currSpecVar=_specVarNumbers.pop();
      }
    }
    //let's find a node we haven't been to...
    while(curr==0 && _alternatives.isNonEmpty()) {
      void* currAlt=_alternatives.pop();
      if(!currAlt) {
	//there's no alternative at this level, we have to backtrack
	_nodeTypes.pop();
	_specVarNumbers.pop();
	if(_alternatives.isNonEmpty()) {
	  _subst.backtrack();
	}
	continue;
      }

      NodeAlgorithm parentType=_nodeTypes.top();

      //proper term nodes that we want to enter don't appear
      //on _alternatives stack (as we always enter them first)
      if(parentType==UNSORTED_LIST) {
	Node** alts=static_cast<Node**>(currAlt);
	while(*alts && !(*alts)->term.isVar()) {
	  alts++;
	}
	curr=*(alts++);
	while(*alts && !(*alts)->term.isVar()) {
	  alts++;
	}
	if(*alts) {
	  _alternatives.push(alts);
	  sibilingsRemain=true;
	} else {
	  sibilingsRemain=false;
	}
      } else {
	ASS_EQ(parentType,SKIP_LIST)
	NodeList* alts=static_cast<NodeList*>(currAlt);
	if(alts->head()->term.isVar()) {
	  curr=alts->head();
	  if(alts->tail() && alts->second()->term.isVar()) {
	    _alternatives.push(alts->tail());
	    sibilingsRemain=true;
	  } else {
	    sibilingsRemain=false;
	  }
	}
      }

      if(sibilingsRemain) {
	currSpecVar=_specVarNumbers.top();
      } else {
	_nodeTypes.pop();
	currSpecVar=_specVarNumbers.pop();
      }
      if(curr) {
	break;
      }
    }
    if(!curr) {
      //there are no other alternatives
      return false;
    }
    if(!_subst.matchNext(currSpecVar, curr->term, sibilingsRemain)) {	//[1]
      //match unsuccessful, try next alternative
      curr=0;
      if(!sibilingsRemain && _alternatives.isNonEmpty()) {
	_subst.backtrack();
      }
      continue;
    }
    while(!curr->isLeaf() && curr->algorithm()==UNSORTED_LIST && static_cast<UArrIntermediateNode*>(curr)->_size==1) {
      //a node with only one child, we don't need to bother with backtracking here.
      unsigned specVar=static_cast<UArrIntermediateNode*>(curr)->childVar;
      curr=static_cast<UArrIntermediateNode*>(curr)->_nodes[0];
      ASS(curr);
      ASSERT_VALID(*curr);
      if(!_subst.matchNext(specVar, curr->term, false)) {
	//matching failed, let's go back to the node, that had multiple children
	//_subst.backtrack();
	if(sibilingsRemain || _alternatives.isNonEmpty()) {
	  //this vacktrack can happen for two different reasons and have two different meanings:
	  //either matching at [1] was separated from the previous one and we're backtracking it,
	  //or it was not, which means it had no sibilings and we're backtracking from its parent.
	  _subst.backtrack();
	}
        curr=0;
        goto main_loop_start;
      }
    }
    if(curr->isLeaf()) {
      //we've found a leaf
      _ldIterator=static_cast<Leaf*>(curr)->allChildren();
      _inLeaf=true;
      return true;
    }

    //let's go to the first child
    sibilingsRemain=enterNode(curr);
  }
}

/**
 * Enter into specified node. This means that if @b node has any admissible
 * children, return one of them and into @b _alternatives push pointer to a list,
 * that will allow retrieving the others. A zero pointer can be pushed onto
 * @b _alternatives, if there isn't more than one admissible child, if there is
 * none, zero pointer should be also returned.
 */
bool SubstitutionTree::FastGeneralizationsIterator::enterNode(Node*& curr)
{
  IntermediateNode* inode=static_cast<IntermediateNode*>(curr);
  NodeAlgorithm currType=inode->algorithm();

  TermList binding=_subst.getSpecVarBinding(inode->childVar);
  curr=0;

  if(currType==UNSORTED_LIST) {
    Node** nl=static_cast<UArrIntermediateNode*>(inode)->_nodes;
    if(binding.isTerm()) {
      unsigned bindingFunctor=binding.term()->functor();
      //let's first skip proper term nodes at the beginning...
      while(*nl && (*nl)->term.isTerm()) {
        //...and have the one that interests us, if we encounter it.
        if(!curr && (*nl)->term.term()->functor()==bindingFunctor) {
          curr=*nl;
        }
        nl++;
      }
      if(!curr && *nl) {
        //we've encountered a variable node, but we still have to check, whether
        //the one proper term node, that interests us, isn't here
        Node** nl2=nl+1;
        while(*nl2) {
          if((*nl2)->term.isTerm() && (*nl2)->term.term()->functor()==bindingFunctor) {
            curr=*nl2;
            break;
          }
          nl2++;
        }
      }
    } else {
      //let's first skip proper term nodes at the beginning
      while(*nl && (*nl)->term.isTerm()) {
        nl++;
      }
    }
    if(!curr && *nl) {
      curr=*(nl++);
      while(*nl && (*nl)->term.isTerm()) {
	nl++;
      }
    }
    if(curr) {
      _specVarNumbers.push(inode->childVar);
    }
    if(*nl) {
      _alternatives.push(nl);
      _nodeTypes.push(currType);
      return true;
    }
  } else {
    NodeList* nl;
    ASS_EQ(currType, SKIP_LIST);
    nl=static_cast<SListIntermediateNode*>(inode)->_nodes.toList();
    if(binding.isTerm()) {
      Node** byTop=inode->childByTop(binding, false);
      if(byTop) {
	curr=*byTop;
      }
    }
    if(!curr && nl->head()->term.isVar()) {
      curr=nl->head();
      nl=nl->tail();
    }
    //in SkipList nodes variables are only at the beginning
    //(so if there aren't any, there aren't any at all)
    if(nl && nl->head()->term.isTerm()) {
      nl=0;
    }
    if(curr) {
      _specVarNumbers.push(inode->childVar);
    }
    if(nl) {
      _alternatives.push(nl);
      _nodeTypes.push(currType);
      return true;
    }
  }
  return false;
}

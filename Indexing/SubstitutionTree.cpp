/**
 * @file SubstitutionTree.cpp
 * Implements class SubstitutionTree.
 *
 * @since 16/08/2008 flight Sydney-San Francisco
 */

#include <utility>

#include "../Kernel/Term.hpp"
#include "../Kernel/Renaming.hpp"
#include "../Kernel/SubstHelper.hpp"
#include "../Lib/BinaryHeap.hpp"
#include "../Lib/Metaiterators.hpp"
#include "../Lib/Environment.hpp"
#include "../Lib/Recycler.hpp"
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
  : _numberOfTopLevelNodes(nodes),
    _nextVar(0)
{
  CALL("SubstitutionTree::SubstitutionTree");

  if(nodes == 0) {
    _nodes=0;
    return;
  }
  _nodes = new(ALLOC_KNOWN(nodes*sizeof(Node*),"SubstitutionTree::Node"))
                Node*[nodes];
  for (int i = nodes-1;i >= 0;i--) {
    _nodes[i] = 0;
  }
} // SubstitutionTree::SubstitutionTree

/**
 * Destroy the substitution tree.
 * @warning does not destroy nodes yet
 * @since 16/08/2008 flight Sydney-San Francisco
 */
SubstitutionTree::~SubstitutionTree()
{
  CALL("SubstitutionTree::~SubstitutionTree");
  if(_nodes) {
    ASS_ALLOC_TYPE(_nodes, "SubstitutionTree::Node");

    for (int i = _numberOfTopLevelNodes-1; i>=0; i--) {
      if(_nodes[i]!=0) {
	delete _nodes[i];
      }
    }

    DEALLOC_KNOWN(_nodes,
	    _numberOfTopLevelNodes*sizeof(Node*),
	    "SubstitutionTree::Node");
  }
} // SubstitutionTree::~SubstitutionTree

/**
 * Store initial bindings of term @b t into @b bq.
 *
 * This method is used for insertions and deletions.
 */
void SubstitutionTree::getBindings(Term* t, BindingQueue& bq)
{
  Binding bind;
  TermList* args=t->args();

  int nextVar = 0;
  while (! args->isEmpty()) {
    if (_nextVar <= nextVar) {
      _nextVar = nextVar+1;
    }
    bind.var = nextVar++;
    bind.term = args;
    bq.insert(bind);
    args = args->next();
  }
}

typedef pair<TermList*, TermList*> SplitPoint;
struct SplitPointComparator
{
  inline
  static int rate(TermList* trm)
  {
    return trm->isTerm() ? 1 : 0;
  }
  inline
  static Comparison compare(const SplitPoint& sp1, const SplitPoint& sp2)
  {
    int sc1=rate(sp1.first)+rate(sp1.second);
    int sc2=rate(sp2.first)+rate(sp2.second);
    return Int::compare(sc1, sc2);
  }
};
typedef BinaryHeap<SplitPoint,SplitPointComparator> SplitPointHeap;

/**
 * Insert an entry to the substitution tree.
 *
 * @b pnode is pointer to root of tree corresponding to
 * top symbol of the term/literal being inserted, and
 * @b bh contains its arguments.
 */
void SubstitutionTree::insert(Node** pnode,BindingQueue& bh,LeafData ld)
{
  CALL("SubstitutionTree::insert/3");

  if(*pnode == 0) {
    if(bh.isEmpty()) {
      *pnode=createLeaf();
    } else {
      *pnode=createIntermediateNode();
    }
  }
  if(bh.isEmpty()) {
    ASS((*pnode)->isLeaf());
    ensureLeafEfficiency(reinterpret_cast<Leaf**>(pnode));
    static_cast<Leaf*>(*pnode)->insert(ld);
    return;
  }

  start:
  Binding bind=bh.pop();
  TermList* term=bind.term;

  ASS(! (*pnode)->isLeaf());
  IntermediateNode* inode = static_cast<IntermediateNode*>(*pnode);

  //Into pparent we store the node, we might be inserting into.
  //So in the case we do insert, we might check whether this node
  //needs expansion.
  Node** pparent=pnode;
  pnode=inode->childByTop(term,true);

  if (*pnode == 0) {
    while (!bh.isEmpty()) {
      IntermediateNode* inode = createIntermediateNode(term);
      *pnode = inode;

      bind = bh.pop();
      term=bind.term;
      pnode = inode->childByTop(term,true);
    }
    Leaf* lnode=createLeaf(term);
    *pnode=lnode;
    lnode->insert(ld);

    ensureIntermediateNodeEfficiency(reinterpret_cast<IntermediateNode**>(pparent));
    return;
  }


  TermList* tt = term;
  TermList* ss = &(*pnode)->term;

  ASS(TermList::sameTop(ss, tt));

  if (tt->sameContent(ss)) {
    if (bh.isEmpty()) {
      ASS((*pnode)->isLeaf());
      ensureLeafEfficiency(reinterpret_cast<Leaf**>(pnode));
      Leaf* leaf = static_cast<Leaf*>(*pnode);
      leaf->insert(ld);
      return;
    }
    goto start;
  }

  static SplitPointHeap splitPoints;
  splitPoints.reset();

  // ss is the term in node, tt is the term to be inserted
  // ss and tt have the same top symbols but are not equal
  // create the common subterm of ss,tt and an alternative node
  Stack<TermList*> subterms(64);
  for (;;) {
    if (!ss->sameContent(tt) && TermList::sameTop(ss,tt)) {
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
      if (! TermList::sameTop(ss,tt)) {
	if(!ss->isSpecialVar()) {
	  splitPoints.insert(SplitPoint(ss,tt));
	} else {
	  unsigned x=ss->var();
	  Binding bind(x,tt);
	  bh.insert(bind);
	}
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

  while(!splitPoints.isEmpty()) {
    SplitPoint sp=splitPoints.pop();
    unsigned x = _nextVar++;
    Node::split(pnode, sp.first, x);
    Binding bind(x,sp.second);
    bh.insert(bind);
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
void SubstitutionTree::remove(Node** pnode,BindingQueue& bh,LeafData ld)
{
  CALL("SubstitutionTree::remove-2");

  ASS(*pnode);

  Stack<Node**> history(1000);

  while (! bh.isEmpty()) {
    history.push(pnode);

    ASS (! (*pnode)->isLeaf());
    IntermediateNode* inode=static_cast<IntermediateNode*>(*pnode);

    Binding bind = bh.pop();
    TermList* t = bind.term;

    pnode=inode->childByTop(t,false);
    ASS(pnode);

    TermList* s = &(*pnode)->term;
    ASS(TermList::sameTop(s,t));

    if (s->content() == t->content()) {
      continue;
    }

    ASS(! s->isVar());
    TermList* ss = s->term()->args();
    ASS(!ss->isEmpty());

    // computing the disagreement set of the two terms
    Stack<TermList*> subterms(120);

    subterms.push(ss);
    subterms.push(t->term()->args());
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
      if (ss->content() == tt->content()) {
	continue;
      }
      if (ss->isVar()) {
	ASS(ss->isSpecialVar());
	Binding b(ss->var(),const_cast<TermList*>(tt));
	bh.insert(b);
	continue;
      }
      ASS(! t->isVar());
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
      parent->remove(&term);
      delete node;
      pnode=history.pop();
      ensureIntermediateNodeEfficiency(reinterpret_cast<IntermediateNode**>(pnode));
    }
  }
} // SubstitutionTree::remove


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
	  res+=getIndentStr(indent) + "Lit: " + Test::Output::toString(ldi.next().literal) + "\n";
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

  for(int tli=0;tli<_numberOfTopLevelNodes;tli++) {
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

  IntermediateNode* newNode = createIntermediateNode(&node->term);
  node->term=*where;
  *pnode=newNode;

  where->makeSpecialVar(var);

  Node** nodePosition=newNode->childByTop(&node->term, true);
  ASS(!*nodePosition);
  *nodePosition=node;
}

void SubstitutionTree::IntermediateNode::loadChildren(NodeIterator children)
{
  CALL("SubstitutionTree::IntermediateNode::loadChildren");

  while(children.hasNext()) {
    Node* ext=*children.next();
    Node** own=childByTop(&ext->term, true);
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

SubstitutionTree::UnificationsIterator::UnificationsIterator(Node* root,
	Term* query, bool retrieveSubstitution, bool reversed)
: literalRetrieval(query->isLiteral()),
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
    svQueue.insert(var);
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
  svQueue.insert(1);
  subst.bindSpecialVar(0,*t->nthArgument(1),NORM_QUERY_BANK);
  svQueue.insert(0);
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

    return QueryResult(&ld, ResultSubstitution::fromMMSubstitution(
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

  if(!n->term.isEmpty()) {
    //n is proper node, not a root

    TermList qt(svQueue.top(), true);

    subst.bdRecord(bd);
    bool success=associate(qt,n->term);
    subst.bdDone();

    if(!success) {
      return false;
    }
    svQueue.backtrackablePop(bd);
    extractSpecialVariables(n->term, bd);
  }
  if(n->isLeaf()) {
    ldIterator=static_cast<Leaf*>(n)->allChildren();
    inLeaf=true;
  } else {
    ASS(!svQueue.isEmpty());
    NodeIterator nit=getNodeIterator(static_cast<IntermediateNode*>(n));
    nodeIterators.backtrackablePush(nit, bd);
  }
  return true;
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

  unsigned specVar=svQueue.top();
  TermList qt=subst.getSpecialVarTop(specVar);
  if(qt.isVar()) {
	return n->allChildren();
  } else {
	Node** match=n->childByTop(&qt, false);
	if(match) {
	  return pvi( getConcatenatedIterator(
			  getSingletonIterator(match),
			  n->variableChildren()) );
	} else {
	  return n->variableChildren();
	}
  }
}

void SubstitutionTree::UnificationsIterator::extractSpecialVariables(
	TermList t, BacktrackData& bd)
{
  CALL("SubstitutionTree::UnificationsIterator::extractSpecialVariables");

  TermList* ts=&t;
  static Stack<TermList*> stack(4);
  for(;;) {
    if(ts->tag()==REF && ts->term()->arity()>0) {
      stack.push(ts->term()->args());
    }
    if(ts->isSpecialVar()) {
      svQueue.backtrackableInsert(ts->var(), bd);
    }
    if(stack.isEmpty()) {
      break;
    }
    ts=stack.pop();
    if(!ts->next()->isEmpty()) {
      stack.push(ts->next());
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

  unsigned specVar=svQueue.top();
  TermList qt=subst.getSpecialVarTop(specVar);
  if(qt.isVar()) {
	return n->variableChildren();
  } else {
	Node** match=n->childByTop(&qt, false);
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

  unsigned specVar=svQueue.top();
  TermList qt=subst.getSpecialVarTop(specVar);
  if(qt.isVar()) {
	return n->allChildren();
  } else {
	Node** match=n->childByTop(&qt, false);
	if(match) {
	  return pvi( getSingletonIterator(match) );
	} else {
	  return NodeIterator::getEmpty();
	}
  }
}




struct SubstitutionTree::GenMatcher::Binder
{
  inline
  Binder(GenMatcher* parent, VarStack* newSpecVars)
  : _parent(parent), _newSpecVars(newSpecVars), _maxVar(parent->_maxVar) {}
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
  inline
  void specVar(unsigned var, TermList term)
  {
    ALWAYS(_parent->_specVars->set(var,term));
    _newSpecVars->push(var);
  }
private:
  GenMatcher* _parent;
  VarStack* _newSpecVars;
  unsigned _maxVar;
};

struct SubstitutionTree::GenMatcher::Applicator
{
  inline
  Applicator(GenMatcher* parent, Renaming* resultNormalizer, Renaming* queryDenormalizer)
  : _parent(parent), _resultNormalizer(resultNormalizer),
  _queryDenormalizer(queryDenormalizer) {}
  TermList apply(unsigned var)
  {
    TermList* cacheEntry;
    if(_cache.getValuePtr(var,cacheEntry)) {
      ASS(_resultNormalizer->contains(var));
      unsigned nvar=_resultNormalizer->get(var);
      ASS(_parent->_bindings->find(nvar));
      TermList norm=_parent->_bindings->get(nvar);
      *cacheEntry=_queryDenormalizer->apply(norm);
    }
    return *cacheEntry;
  }
private:
  GenMatcher* _parent;
  Renaming* _resultNormalizer;
  Renaming* _queryDenormalizer;
  BindingMap _cache;
};

class SubstitutionTree::GenMatcher::Substitution
: public ResultSubstitution
{
public:
  inline
  Substitution(GenMatcher* parent, Renaming* resultNormalizer,
	  Renaming* queryDenormalizer)
  : _parent(parent), _resultNormalizer(resultNormalizer),
  _queryDenormalizer(queryDenormalizer), _applicator(0)
  {}
  inline
  TermList applyToBoundResult(TermList t)
  { return SubstHelper::apply(t, *getApplicator()); }

  inline
  bool isIdentityOnQueryWhenResultBound() {return true;}
private:
  Applicator* getApplicator()
  {
    if(!_applicator) {
      _applicator=new Applicator(_parent, _resultNormalizer, _queryDenormalizer);
    }
    return _applicator;
  }

  GenMatcher* _parent;
  Renaming* _resultNormalizer;
  Renaming* _queryDenormalizer;
  Applicator* _applicator;
};

SubstitutionTree::GenMatcher::GenMatcher(Term* query)
: _boundVars(256), _poppedSpecVars(256), _poppedSpecVarIndexes(256),
_insertedSpecVarIndexes(256)
{
  Recycler::get(_specVarQueue);
  Recycler::get(_specVars);
  Recycler::get(_bindings);

  _maxVar=query->weight()-1;
  _bindings->ensure(query->weight());
}
SubstitutionTree::GenMatcher::~GenMatcher()
{
  Recycler::release(_bindings);
  Recycler::release(_specVars);
  Recycler::release(_specVarQueue);
}


bool SubstitutionTree::GenMatcher::matchNext(TermList nodeTerm)
{
  CALL("SubstitutionTree::GenMatcher::matchNext");


  unsigned popBacktrackIndex;
  unsigned specVar=_specVarQueue->backtrackablePop(popBacktrackIndex);

  _poppedSpecVars.push(specVar);
  _poppedSpecVarIndexes.push(popBacktrackIndex);
  _boundVars.push(BACKTRACK_SEPARATOR);
  _insertedSpecVarIndexes.push(BACKTRACK_SEPARATOR);

  TermList queryTerm=_specVars->get(specVar);

  if(nodeTerm.isTerm() && nodeTerm.term()->shared()) {
    if(nodeTerm.term()->ground()) {
      return nodeTerm==queryTerm;
    }
  }

  static VarStack newSpecVars(32);
  newSpecVars.reset();

  Binder binder(this,&newSpecVars);
  bool success=MatchingUtils::matchTerms(nodeTerm, queryTerm, binder);

  if(success) {
    while(newSpecVars.isNonEmpty()) {
      unsigned insertBacktrackIndex=_specVarQueue->backtrackableInsert(newSpecVars.pop());
      _insertedSpecVarIndexes.push(insertBacktrackIndex);
    }
  }
  return success;
}

void SubstitutionTree::GenMatcher::backtrack()
{
  for(;;) {
    unsigned specVarIndex=_insertedSpecVarIndexes.pop();
    if(specVarIndex==BACKTRACK_SEPARATOR) {
      break;
    }
    _specVarQueue->backtrackInsert(specVarIndex);
  }
  _specVarQueue->backtrackPop(_poppedSpecVars.pop(),_poppedSpecVarIndexes.pop());
  for(;;) {
    unsigned boundVar=_boundVars.pop();
    if(boundVar==BACKTRACK_SEPARATOR) {
      break;
    }
    _bindings->remove(boundVar);
  }
}


ResultSubstitutionSP SubstitutionTree::GenMatcher::getSubstitution(
	Renaming* resultNormalizer, Renaming* queryDenormalizer)
{
  return ResultSubstitutionSP(
	  new Substitution(this, resultNormalizer, queryDenormalizer));
}

SubstitutionTree::FastGeneralizationsIterator::FastGeneralizationsIterator(Node* root,
	Term* query, bool retrieveSubstitution, bool reversed)
: _subst(query), _literalRetrieval(query->isLiteral()), _retrieveSubstitution(retrieveSubstitution),
  _inLeaf(false), _ldIterator(LDIterator::getEmpty()), _nodeIterators(8)
{
  CALL("SubstitutionTree::FastGeneralizationsIterator::FastGeneralizationsIterator");

  if(!root) {
    return;
  }

  Renaming queryNormalizer;
  queryNormalizer.normalizeVariables(query);
  Term* queryNorm=queryNormalizer.apply(query);

  if(_retrieveSubstitution) {
    _queryDenormalizer.makeInverse(queryNormalizer);
  }

  if(reversed) {
    createReversedInitialBindings(queryNorm);
  } else {
    createInitialBindings(queryNorm);
  }

  enter(root);
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
	    _subst.getSubstitution(&_resultNormalizer, &_queryDenormalizer));
  } else {
    return QueryResult(&ld, ResultSubstitutionSP());
  }
}


bool SubstitutionTree::FastGeneralizationsIterator::findNextLeaf()
{
  CALL("SubstitutionTree::FastGeneralizationsIterator::findNextLeaf");

  if(_nodeIterators.isEmpty()) {
    //There are no node iterators in the stack, so there's nowhere
    //to look for the next leaf.
    //This shouldn't hapen during the regular retrieval process, but it
    //can happen when there are no literals inserted for a predicate,
    //or when predicates with zero arity are encountered.
    return false;
  }

  if(_inLeaf) {
    //Leave the current leaf
    _subst.backtrack();
    _inLeaf=false;
  }

  do {
    while(!_nodeIterators.top().hasNext()) {
      _nodeIterators.pop();
      if(_nodeIterators.isEmpty()) {
        return false;
      }
      _subst.backtrack();
    }
    Node* n=*_nodeIterators.top().next();
    bool success=enter(n);
    if(!success) {
      _subst.backtrack();
      continue;
    }
  } while(!_inLeaf);
  return true;
}

bool SubstitutionTree::FastGeneralizationsIterator::enter(Node* n)
{
  CALL("SubstitutionTree::FastGeneralizationsIterator::enter");

  if(!n->term.isEmpty()) {
    //n is proper node, not a root

    bool success=_subst.matchNext(n->term);

    if(!success) {
      return false;
    }
  }
  if(n->isLeaf()) {
    _ldIterator=static_cast<Leaf*>(n)->allChildren();
    _inLeaf=true;
  } else {
    NodeIterator nit=getNodeIterator(static_cast<IntermediateNode*>(n));
    _nodeIterators.push(nit);
  }
  return true;
}

SubstitutionTree::NodeIterator
  SubstitutionTree::FastGeneralizationsIterator::getNodeIterator(IntermediateNode* n)
{
  CALL("SubstitutionTree::FastGeneralizationsIterator::getNodeIterator");

  TermList qt=_subst.getNextSpecVarBinding();
  if(qt.isVar()) {
	return n->allChildren();
  } else {
	Node** match=n->childByTop(&qt, false);
	if(match) {
	  return pvi( getConcatenatedIterator(
			  getSingletonIterator(match),
			  n->variableChildren()) );
	} else {
	  return n->variableChildren();
	}
  }
}

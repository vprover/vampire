/**
 * @file SubstitutionTree.cpp
 * Implements class SubstitutionTree.
 *
 * @since 16/08/2008 flight Sydney-San Francisco
 */

#include "../Kernel/Clause.hpp"
#include "../Kernel/Term.hpp"
#include "../Lib/BinaryHeap.hpp"

#ifdef VDEBUG
#include <iostream>
#include "../Kernel/Signature.hpp"
#include "../Lib/Environment.hpp"
#include "../Lib/Int.hpp"
#include "../Test/Output.hpp"

string SingleTermListToString(const TermList* ts);

#endif

#include "SubstitutionTree.hpp"

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
  ASS(nodes > 0);

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

  DEALLOC_KNOWN(_nodes,
		_numberOfTopLevelNodes*sizeof(Node*),
		"SubstitutionTree::Node");
} // SubstitutionTree::~SubstitutionTree


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

void SubstitutionTree::insert(Literal* lit, Clause* cls)
{ 
  BindingQueue bq;
  getBindings(lit, bq);
  insert(_nodes+getRootNodeIndex(lit), bq, LeafData(cls, lit));
}
void SubstitutionTree::remove(Literal* lit, Clause* cls)
{
  BindingQueue bq;
  getBindings(lit, bq);
  remove(_nodes+getRootNodeIndex(lit), bq, LeafData(cls, lit));
}

void SubstitutionTree::insert(TermList* term, Clause* cls)
{
  ASS(!term->isEmpty());
  ASS(!term->isSpecialVar());
  
  BindingQueue bq;
  getBindings(term, bq);
  
  insert(_nodes+getRootNodeIndex(term), bq, LeafData(cls, reinterpret_cast<void*&>(*term)));
}

void SubstitutionTree::remove(TermList* term, Clause* cls)
{
  ASS(!term->isEmpty());
  ASS(!term->isSpecialVar());
  
  BindingQueue bq;
  getBindings(term, bq);
  
  remove(_nodes+getRootNodeIndex(term), bq, LeafData(cls, reinterpret_cast<void*&>(*term)));
}

/**
 * Auxiliary function for substitution tree insertion.
 * @since 16/08/2008 flight Sydney-San Francisco
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

  ASS(sameTop(ss, tt));

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

  // ss is the term in node, tt is the term to be inserted
  // ss and tt have the same top symbols but are not equal
  // create the common subterm of ss,tt and an alternative node
  Stack<TermList*> subterms(64);
  for (;;) {
    if (!ss->sameContent(tt) && sameTop(ss,tt)) {
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
      if (! sameTop(ss,tt)) {
	int x;
	if(!ss->isSpecialVar()) { 
	  x = _nextVar++;
	  Node::split(pnode, ss,x);
	} else {
	  x=ss->var();
	}
	Binding bind(x,tt);
	bh.insert(bind);
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
  
  goto start;
} // // SubstitutionTree::insert

/**
 * Return true if @b ss and @b tt have the same top symbols, that is,
 * either both are the same variable or both are complex terms with the
 * same function symbol. 
 * @since 16/08/2008 flight Sydney-San Francisco
 */
bool SubstitutionTree::sameTop(const TermList* ss,const TermList* tt)
{
  if (ss->isVar()) {
    return ss->sameContent(tt);
  }
  if (tt->isVar()) {
    return false;
  }
  return ss->term()->functor() == tt->term()->functor();
}

/*
 * Remove a clause from the substitution tree.
 * @since 16/08/2008 flight San Francisco-Seattle
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
    ASS(sameTop(s,t));

    if (s->content() == t->content()) {
      continue;
    }
    
    ASS(! s->isVar());
    const TermList* ss = s->term()->args();
    ASS(!ss->isEmpty());

    // computing the disagreement set of the two terms
    TermStack subterms(120);

    subterms.push(ss);
    subterms.push(t->term()->args());
    while (! subterms.isEmpty()) {
      const TermList* tt = subterms.pop();
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

string SubstitutionTree::toString() const
{
  CALL("SubstitutionTree::toString");

  string res;
  
  for(int tli=0;tli<_numberOfTopLevelNodes;tli++) {
    res+=Int::toString(tli);
    res+=":\n";
    
    Stack<int> indentStack(10);
    Stack<Node*> stack(10);
    
    stack.push(_nodes[tli]);
    indentStack.push(1);
    
    while(stack.isNonEmpty()) {
      Node* node=stack.pop();
      int indent=indentStack.pop();

      if(!node) {
	continue;
      }
      if(node->term.content()) {
	res+=getIndentStr(indent)+Test::Output::singleTermListToString(&node->term)+"\n";
      }

      if(node->isLeaf()) {
	Leaf* lnode = static_cast<Leaf*>(node);
	LDIterator ldi(lnode->allChildren());
	
	while(ldi.hasNext()) {
	  res+=getIndentStr(indent) + "Cl: " + Test::Output::toString(ldi.next().clause) + "\n";
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


bool SubstitutionTree::ResultIterator::findNextLeaf()
{
  CALL("SubstitutionTree::ResultIterator::findNextLeaf");

  if(inLeaf) {
    //Leave the current leaf
    btStack.pop().backtrack();
    inLeaf=false;
  }

  ASS(btStack.length()+1==nodeIterators.length());

  do {
    while(!nodeIterators.top().hasNext() && !btStack.isEmpty()) {
      //backtrack undos everything that enter(...) method has done,
      //so it also pops one item out of the nodeIterators stack
      btStack.pop().backtrack();
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
      btStack.push(bd);
    }
  } while(!inLeaf);
  return true;
}

bool SubstitutionTree::ResultIterator::enter(Node* n, BacktrackData& bd)
{
  CALL("SubstitutionTree::ResultIterator::enter");

  if(!n->term.isEmpty()) {
    //n is proper node, not a root
    Binding bind=bQueue.top();
    TermList qt;

    TermList nt;
    subst.apply(&n->term, 1, nt);

    bool success=associate(qt, nt, bd);

    if(!success) {
      return false;
    }

    bQueue.backtrackablePop(bd);
  }
  if(n->isLeaf()) {
    ldIterator=static_cast<Leaf*>(n)->allChildren();
    inLeaf=true;
  } else {
    ASS(!bQueue.isEmpty());
    TermList qt=*bQueue.top().term;
    NodeIterator nit=getNodeIterator(static_cast<IntermediateNode*>(n), qt);
    nodeIterators.backtrackablePush(nit, bd);
  }
  return true;
}

bool SubstitutionTree::ResultIterator::associate(TermList qt, TermList nt, BacktrackData& bd)
{
  CALL("SubstitutionTree::ResultIterator::associate");

  BacktrackData localBd;
  TermList* ss=&nt;
  TermList* tt=&qt;

  bool mismatch=false;
  
  Stack<TermList*> subterms(64);
  for (;;) {
    
    if (!ss->sameContent(tt) && sameTop(ss,tt)) {
      // ss and tt have the same tops and are different, so must be non-variables
      ASS(! ss->isVar());
      ASS(! tt->isVar());

      Term* s = ss->term();
      Term* t = tt->term();

      ASS(s->arity() > 0);
      ASS(s->functor() == t->functor());

      ss = s->args();
      tt = t->args();
      if (ss->next()->isEmpty()) {
        continue;
      }
      subterms.push(ss->next());
      subterms.push(tt->next());
    } else {
      if ( ss->isTerm() && !ss->term()->shared() && tt->isVar()) {
	if(handleNotSharedTermAndVar(*tt, *ss, localBd)) {
	  //the content of tt and ss have changed, so we have to reexamine them
	  continue;
	} else {
          mismatch=true;
          break;
	}
      }
      
      if (! sameTop(ss,tt)) {
        int x;
        if(ss->isSpecialVar()) { 
          Binding bind(x,tt);
          bQueue.backtrackableInsert(bind, localBd);
        } else {
          bool handled=handleMismatch(*tt, *ss, localBd);
          if(!handled) {
            mismatch=true;
            break;
          }
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
  if(mismatch) {
    localBd.backtrack();
    return false;
  }
  localBd.commitTo(bd);
  return true;
}
